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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Lept_chain Lept_gmax_defs
  Gm_iface Gq_obj Gq_iface Gq_cmap_iface Gq_d2bpp_defs Gq_dt2tab Gq_dither2_l1 Gq_dither2_line Gq_dither2_rows Gq_cmaplin Gq_d2bpp_cmdefs Gq_d2bpp_mid.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Lept_fuzzkit Lept_deserkit Gm_kit Gm_livekit Gm_livekit2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Gq_d2bpp_exit.
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
Local Ltac park_ne := repeat match goal with H : (?a <> ?b) |- _ => lazymatch type of a with Z => change (a <> b) with (parked (a <> b)) in H end end.

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
Lemma live_destroy_d2 : forall (live : list (Z * Z)) pixd dat rs cmd arr na v cv,
  p_data v = dat -> p_cmap v = cmd -> c_arr cv = arr -> dat <> 0 -> cmd <> 0 -> arr <> 0 ->
  dat <> pixd -> dat <> arr -> dat <> cmd -> arr <> pixd -> cmd <> pixd -> cmd <> arr ->
  (forall e, In e live -> fst e <> pixd) -> (forall e, In e live -> fst e <> dat) ->
  (forall e, In e live -> fst e <> cmd) -> (forall e, In e live -> fst e <> arr) ->
  live_destroy pixd v cv ((arr, na) :: (cmd, 24) :: (dat, rs) :: (pixd, 64) :: live) = live.
Proof.
  intros live pixd dat rs cmd arr na v cv ED EC EA DNZ CNZ ANZ DP DA DC AP CP CA F1 F2 F3 F4.
  unfold live_destroy. rewrite ED, EC, EA. replace (cmd =? 0) with false by (symmetry; apply Z.eqb_neq; exact CNZ).
  rewrite (rm_opt_nz dat _ DNZ), (rm_opt_nz arr _ ANZ), (rm_opt_nz cmd _ CNZ).
  rewrite (live_remove_other dat arr na) by (intros E; exact (DA (eq_sym E))).
  rewrite (live_remove_other dat cmd 24) by (intros E; exact (DC (eq_sym E))).
  rewrite (live_remove_head dat rs).
  rewrite (live_remove_other dat pixd 64) by (intros E; exact (DP (eq_sym E))).
  rewrite (live_remove_fresh dat live F2).
  rewrite (live_remove_head arr na).
  rewrite (live_remove_other arr cmd 24) by (intros E; exact (CA E)).
  rewrite (live_remove_other arr pixd 64) by (intros E; exact (AP (eq_sym E))).
  rewrite (live_remove_fresh arr live F4).
  rewrite (live_remove_head cmd 24).
  rewrite (live_remove_other cmd pixd 64) by (intros E; exact (CP (eq_sym E))).
  rewrite (live_remove_fresh cmd live F3).
  rewrite (live_remove_head pixd 64).
  exact (live_remove_fresh pixd live F1).
Qed.
(* [comment removed for export] *)
Lemma live_destroy_d2t : forall (live : list (Z * Z)) pixt dtt rst cmd arr na vt cvt,
  p_data vt = dtt -> p_cmap vt = 0 -> dtt <> 0 -> dtt <> pixt -> arr <> dtt -> cmd <> dtt -> arr <> pixt -> cmd <> pixt ->
  (forall e, In e live -> fst e <> pixt) -> (forall e, In e live -> fst e <> dtt) ->
  live_destroy pixt vt cvt ((arr, na) :: (cmd, 24) :: (dtt, rst) :: (pixt, 64) :: live) = (arr, na) :: (cmd, 24) :: live.
Proof.
  intros live pixt dtt rst cmd arr na vt cvt ED EC DNZ DP AD CD AP CP F1 F2.
  unfold live_destroy. rewrite ED, EC. cbn [Z.eqb]. unfold rm_opt at 2. unfold rm_opt at 1. cbn [Z.eqb].
  rewrite (rm_opt_nz dtt _ DNZ).
  rewrite (live_remove_other dtt arr na) by (exact AD).
  rewrite (live_remove_other dtt cmd 24) by (exact CD).
  rewrite (live_remove_head dtt rst).
  rewrite (live_remove_other dtt pixt 64) by (intros E; exact (DP (eq_sym E))).
  rewrite (live_remove_fresh dtt live F2).
  rewrite (live_remove_other pixt arr na) by (exact AP).
  rewrite (live_remove_other pixt cmd 24) by (exact CP).
  rewrite (live_remove_head pixt 64).
  rewrite (live_remove_fresh pixt live F1). reflexivity.
Qed.
(* [comment removed for export] *)
Ltac chunk_side fr b FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx :=
  repeat match goal with H : parked (fr + 256 <= b \/ _ <= fr) |- _ => unpark H; revert H end;
  repeat match goal with H : parked (b + _ <= fr / 8 + 2147450880 \/ _ <= b) |- _ => unpark H; revert H end;
  repeat match goal with H : parked (b + _ <= 2147446784 \/ _ <= b) |- _ => unpark H; revert H end;
  repeat match goal with H : b + _ <= rt_sp0 _ _ - 8388608 |- _ => revert H end;
  unpark FRSH; unfold shad, SHB in *; clear - Hx FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0; intros; cbn [outside]; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
(* [comment removed for export] *)
Ltac fcell_side fr b Hx :=
  repeat match goal with H : parked (fr + 256 <= b \/ _ <= fr) |- _ => unpark H; revert H end; clear - Hx; intros; cbn [outside]; repeat split; try exact I; lia.

Section D2BPPC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis PCS : pixCreate_sure_cps RT.
Hypothesis PCR : pixCopyResolution_cps RT.
Hypothesis PCI : pixCopyInputFormat_cps RT.
Hypothesis PRC : pixRemoveColormap_gray_cps RT.
Hypothesis PDR : pixDestroy_rc_cps RT.
Hypothesis DES : pixDestroy_cps RT.
Hypothesis CML : pixcmapCreateLinear24_cps RT.
Hypothesis SCM : pixSetColormap_cps RT.
Hypothesis CMF : d2_cmfree_cps RT.

(* [comment removed for export] *)
Local Ltac fold_pres usp := fold_ag ltac:(fun Hx => hnf in Hx; destruct Hx as [Hx1 Hx2];
  apply (aclient_mono _ _ usp _ _ _ _ Hx1); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| clear; lia]).
Local Ltac fold_pres2 usp side2 := fold_ag ltac:(fun Hx => hnf in Hx; destruct Hx as [Hx1 Hx2]; split;
  [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| clear; lia] | side2 Hx1 Hx2]).

(* [comment removed for export] *)
Local Ltac agf_side PFS NFA LOR Hx :=
  let P1 := fresh "P1" in let N1 := fresh "N1" in let N2 := fresh "N2" in let Hx1 := fresh "Hx1" in let Hx2 := fresh "Hx2" in
  pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [Hx1 Hx2]; cbn [outside]; unfold shad, SHB in *;
  clear - P1 N1 N2 Hx2 LOR; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].

(* [comment removed for export] *)
Local Ltac nodup4 := repeat first [ apply NoDup_nil_2 | apply NoDup_cons_2; [ repeat (apply (proj2 (stdpp.list_basics.list.not_elem_of_cons _ _ _)); split; [congruence|]); apply stdpp.list_basics.list.not_elem_of_nil |] ].

(* [comment removed for export] *)
Local Ltac carry AG H acl side :=
  unfold hid in H;
  lazymatch type of AG with agree_on _ ?ma ?mb => lazymatch type of H with rw_cells _ ma ?A ?cs =>
    apply (rw_cells_agree_nw asegs ma mb A cs) in H;
    [| eapply agree_sub; [exact AG|]; cbv beta; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
       unfold pix_cells_rc, pix_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; first [split; [acl x Hx| cbn [outside]; side Hx] | acl x Hx] ] end end.

(* [comment removed for export] *)
Local Ltac call_ok_tac2 SPA :=
  unfold call_ok; rewrite ?unsigned_lit by ul; split; [eassumption|];
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; repeat split; first [ul | clear - SPA; Z.div_mod_to_equations; lia].

(* [comment removed for export] *)
Local Ltac carry_mu MU H side :=
  unfold hid in H;
  lazymatch type of MU with munch ?W ?ma ?mb => lazymatch type of H with rw_cells _ ma ?A ?cs =>
    apply (rw_cells_agree_nw asegs ma mb A cs) in H;
    [| eapply agree_sub; [exact (agree_of_munch W ma mb (outside W) MU (fun x Hx => Hx))|]; cbv beta;
       let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
       unfold pix_cells_rc, pix_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; side Hx ] end end.

(* [comment removed for export] *)
Local Ltac find_in := repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; cbn [In]; repeat first [left; reflexivity | assumption | right].
(* [comment removed for export] *)
Local Ltac fr_side fr Hx := repeat match goal with Hf : parked (fr + 256 <= ?b \/ _ <= fr) |- _ => unfold parked in Hf; revert Hf end;
  repeat match goal with E : ?r = 4 * (_ * _) |- _ => revert E end; clear - Hx; intros; lia.
Local Ltac sh_side fr FR64 Hx := repeat match goal with Hf : parked (?b + _ <= fr / 8 + 2147450880 \/ (fr + 256) / 8 + 2147450880 <= ?b) |- _ => unfold parked in Hf; revert Hf end;
  repeat match goal with E : ?r = 4 * (_ * _) |- _ => revert E end; unfold shad, SHB in *; clear - Hx FR64; intros; first [lia | Z.div_mod_to_equations; lia].

(* [comment removed for export] *)
Local Ltac sigma_gc RT S0 Sx :=
  repeat match goal with S : rts RT |- _ =>
    tryif constr_eq S S0 then fail else tryif constr_eq S Sx then fail else
      (repeat match goal with H : context [S] |- _ => clear H end; clear S) end.

Local Ltac eqv :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity.

Lemma d2bpp_spec_c0 : d2bpp_spec_case RT 0.
Proof using AF GP RC RERR PCS PCR PCI PRC PDR DES CML SCM CMF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    FDO MST -> -> -> -> -> POBJ VDATA CNZ D8 UC RAF RAS ENV RES AL.
  unfold lpost_f, lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  unfold D2_COST, OP_COST, is_d8, MSG_COST in *. cbn [Z.eqb Pos.eqb] in CRB.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixDitherTo2bppSpec, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pix + 20, pix + 24)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pix 64.
  chunk_facts RT AF GP (p_data v) (rsize v).
  unfold pix_cells in PXC.
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> outside [(pix + 20, pix + 24)] a -> PF a).
  { intros q k a Hq Ha Ho. split; [| exact Ho]. right; right; left; exists q, k; split; [exact Hq| lia]. }
  (* [comment removed for export] *)
  assert (PSRC : forall (lv : list (Z * Z)) (rc : Z) (mc : mem), (forall e, In e (rt_live RT Σ) -> In e lv) -> agree_on PF m mc ->
            rw_cells asegs mc pix (pix_cells_rc v rc) -> pix_obj_rc lv mc pix v cv rc).
  { intros lv rc mc SUB AG PX. destruct POBJ as (_ & PCH & HOK & PDATA & PCMAP).
    split; [exact PX|]. split; [exact (chunk_mono _ _ _ _ SUB PCH)|]. split; [exact HOK|].
    split; [destruct PDATA as [Z0|(DCH & DN)]; [left; exact Z0| right; split; [exact (chunk_mono _ _ _ _ SUB DCH)| exact DN]]|].
    destruct PCMAP as [Z0|(CO & NN)]; [left; exact Z0| right]. split; [| exact NN].
    apply (cmap_obj_mono _ _ mc _ cv SUB).
    pose proof CO as (_ & (CI & C0 & _) & _).
    apply (cmap_obj_agree (rt_live RT Σ) PF m mc (p_cmap v) cv CO AG). intros a Ha.
    pose proof (live_apart2 RT AF Σ m (p_cmap v) 24 pix 64 ART0 CI PIN ltac:(intros E; inversion E; destruct NN as (N1 & _); exact (N1 ltac:(assumption)))) as DJ.
    split; [right; right; left; exists (p_cmap v), 24; split; [exact CI| exact Ha]| cbn [outside]; split; [clear - DJ Ha; lia| exact I]]. }
  hide POBJ.
  park_disj. park_ne.
  carve_frame 256%nat ST.
  try forget_junk_in (usp + -256). try diet_chains.
  walk_to AF MST [(usp - 256, usp)] [e_stack_malloc 2%nat].
  idtac "MARK at stack_malloc".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_2 RT GP) as SM2; unfold stack_malloc_contract' in SM2; eapply SM2 with (lo := lo); rt_side idtac.
  all: try (clear - CRB; unfold RASTER_COST in CRB; lia).
  all: try call_ok_tac2 SPA.
  }
  after_call RT AF.
  fold_pres usp.
  fframe_open RT AF PF (rt_live RT Σ) usp 2%nat 256 ltac:(fun Ha => exact (proj1 Ha)).
  fframe_chunk RT AF fr 2%nat 256 pix 64.
  fframe_chunk RT AF fr 2%nat 256 (p_data v) (4 * (p_wpl v * p_h v)).
  clear_acc. refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  idtac "MARK frame open".
  try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9f654].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx => agf_side PFS NFA LOR Hx) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH. local_acc FSH fr 8%nat 64 FR64 FR1 ACCD.
  park_disj.
  idtac "MARK header done".
  try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCreate; 0x9f6fc; 0x9f6c4; 0x9f73c; e_stack_malloc 2%nat].
  idtac "MARK after dims".
  try (rewrite D8; brF).
  awalk [e_pixCreate; 0x9f740; 0x9f68c].
  idtac "MARK at pixCreate".
  rewrite ?(sx32_small (p_w v)) by (clear - HW0 HW2; lia). rewrite ?(sx32_small (p_h v)) by (clear - HH0 HH2; lia).
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => agf_side PFS NFA LOR Hx).
  idtac "MARK at_call pixCreate".
  assert (WR : 0 < p_w v <= 20000) by (clear - HW0 HW2; lia). assert (HR : 0 < p_h v <= 20000) by (clear - HH0 HH2; lia).
  (* [comment removed for export] *)
  assert (HAO : hdr_args_ok (p_w v) (p_h v) 2).
  { unfold hdr_args_ok. split; [cbn [In]; tauto|]. split; [exact WR|]. split; [exact HR|].
    pose proof HWPL as QW. rewrite D8 in QW.
    assert (Q1 : 1 <= (p_w v * 2 + 31) / 32 <= (p_w v * 8 + 31) / 32) by (clear - WR; Z.div_mod_to_equations; lia).
    assert (Q2 : (p_w v * 2 + 31) / 32 * p_h v <= (p_w v * 8 + 31) / 32 * p_h v) by (apply Z.mul_le_mono_nonneg_r; clear - Q1 HR; lia).
    rewrite <- QW in Q2. clear - Q1 Q2 HR HRS1. nia. }
  assert (CRD : 2 * RASTER_COST + 64 - 1 <= rt_credit RT Σ) by (clear - CRB; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; lia).
  eapply cps_seq.
  {
  eapply PCS with (lo := lo) (w := p_w v) (h := p_h v) (d := 2).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - split; [clear - WR; lia| reflexivity].
    - split; [clear - HR; lia| reflexivity].
    - split; [clear; lia| reflexivity].
    - exact HAO.
    - lenv_tac.
    - unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; unfold RASTER_COST in *; repeat split; [clear - FRB; lia| clear - LVB; lia| clear - CRB; lia| exact LVP].
  }
  idtac "MARK pixCreate applied".
  after_call RT AF.
  fold_pres2 usp ltac:(fun Hx1 Hx2 => exact I).
  idtac "MARK after pixCreate".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σc; rename A into ARTC end.
  lazymatch goal with H : pix_obj (rt_live RT Σc) _ ?p ?vv _ |- _ => rename H into POD; rename p into pixd; rename vv into v1 end.
  lazymatch goal with H : rt_live RT Σc = _ |- _ => rename H into LVN end.
  lazymatch goal with H : p_w v1 = _ |- _ => rename H into VW end.
  lazymatch goal with H : p_h v1 = _ |- _ => rename H into VH end.
  lazymatch goal with H : p_d v1 = _ |- _ => rename H into VD end.
  lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into VDATA1 end.
  lazymatch goal with H : p_cmap v1 = 0 |- _ => rename H into VCMAP end.
  assert (FRSc : rt_frames RT Σc = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σc = _ |- _ => rewrite E end; exact FRS).
  assert (LVC : rt_live RT Σc = (p_data v1, rsize v1) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVN; repeat match goal with E : rt_live _ _ = rt_live RT Σ |- _ => rewrite E end; reflexivity).
  assert (SP0C : rt_sp0 RT Σc = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRC : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σc) by (repeat match goal with E : rt_credit _ _ = _ |- _ => rewrite E in * end; lazymatch goal with E : _ <= rt_credit RT Σc |- _ => clear - E; lia end).
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
        [ rewrite FRSc; intros e He; right; exact He | rewrite SP0C; ul | exact (proj1 Ha) ]).
  assert (NCD : forall a, PF a -> a < dat \/ dat + rs <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σc _ dat rs (rt_live RT Σ) (rt_frames RT Σ) usp a ARTC DDIN SUBD);
        [ rewrite FRSc; intros e He; right; exact He | rewrite SP0C; ul | exact (proj1 Ha) ]).
  assert (NPS : pix <> pixd) by (exact (proj2 (SUBP (pix, 64) PIN))).
  assert (NDS : pix <> dat) by (exact (proj2 (SUBD (pix, 64) PIN))).
  assert (NSP : p_data v <> pixd) by (exact (proj2 (SUBP (p_data v, 4 * (p_wpl v * p_h v)) DIN))).
  assert (NSD : p_data v <> dat) by (exact (proj2 (SUBD (p_data v, 4 * (p_wpl v * p_h v)) DIN))).
  idtac "MARK names".
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
  fframe_chunk RT AF fr 2%nat 256 pixd 64. fframe_chunk RT AF fr 2%nat 256 dat rs.
  unfold pix_cells in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  assert (EWD : p_wpl v1 = (p_w v * 2 + 31) / 32) by (destruct HOKD as (_ & _ & _ & Q4 & _); rewrite VW, VD in Q4; exact Q4).
  assert (ERS : rs = 4 * (p_wpl v1 * p_h v)) by (unfold rs, rsize; rewrite VH; reflexivity).
  assert (RSD : 0 < 4 * (p_wpl v1 * p_h v) <= 67108864) by (destruct HOKD as (_ & _ & _ & _ & Q5); rewrite VH in Q5; exact Q5).
  hide POD. hide SUBP. hide SUBD. hide HOKD.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK before walk to PCR".
  try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCopyResolution; 0x9ff88].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => agf_side PFS NFA LOR Hx).
  assert (LSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVC; right; right; exact He).
  unfold hid in POD.
  lazymatch goal with PX : rw_cells asegs ?mc pixd _, PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σc _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POD1 : pix_obj (rt_live RT Σc) mc pixd v1 (mkCmapv 0 0 0 0))
      by (destruct POD as (_ & CH & HOK & HD & _); split; [unfold pix_cells; rewrite VW, VH, VD, VCMAP; exact PX| split; [exact CH| split; [exact HOK| split; [exact HD| left; exact VCMAP]]]]);
    assert (POS1 : pix_obj_rc (rt_live RT Σc) mc pix v cv 1) by (exact (PSRC (rt_live RT Σc) 1 mc LSUB AGF PS)) end.
  hide POD.
  idtac "MARK objs for PCR".
  eapply cps_seq.
  {
  eapply PCR with (lo := lo) (pixd := pixd) (pixs := pix) (vd := v1) (vs := v) (cvd := mkCmapv 0 0 0 0) (cvs := cv) (rc := 1).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact POD1.
  - exact POS1.
  - intros E; unfold parked in NPS; apply NPS; symmetry; exact E.
  - lenv_tac.
  }
  idtac "MARK PCR applied".
  clear POD1 POS1.
  lazymatch goal with A : ART RT Σc ?mm |- _ =>
    pose proof (live_apart2 RT AF Σc mm pix 64 pixd 64 A (LSUB _ PIN) PDIN ltac:(intros E; inversion E; unfold parked in NPS; exact (NPS ltac:(assumption)))) as DSP;
    pose proof (live_apart2 RT AF Σc mm pix 64 dat rs A (LSUB _ PIN) DDIN ltac:(intros E; inversion E; unfold parked in NDS; exact (NDS ltac:(assumption)))) as DSD;
    pose proof (live_apart2 RT AF Σc mm pixd 64 dat rs A PDIN DDIN ltac:(intros E; inversion E; unfold parked in DDNE; apply DDNE; symmetry; assumption)) as DPD;
    pose proof (live_apart2 RT AF Σc mm (p_data v) (4 * (p_wpl v * p_h v)) pixd 64 A (LSUB _ DIN) PDIN ltac:(intros E; inversion E; unfold parked in NSP; exact (NSP ltac:(assumption)))) as DRP;
    pose proof (live_apart2 RT AF Σc mm (p_data v) (4 * (p_wpl v * p_h v)) dat rs A (LSUB _ DIN) DDIN ltac:(intros E; inversion E; unfold parked in NSD; exact (NSD ltac:(assumption)))) as DRD end.
  park DSP. park DSD. park DPD. park DRP. park DRD.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with E : rt_live _ _ = rt_live RT Σc |- _ => rewrite E end; apply LSUB; exact He| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  idtac "MARK after PCR".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σr; rename A into ARTR end.
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
  unfold pix_cells in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  assert (LVR : rt_live RT Σr = rt_live RT Σc) by (repeat match goal with E : rt_live RT Σr = _ |- _ => rewrite E end; reflexivity).
  assert (FRSr : rt_frames RT Σr = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σr = _ |- _ => rewrite E end; exact FRSc).
  assert (SP0r : rt_sp0 RT Σr = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRr : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σr) by (lazymatch goal with E : rt_credit RT Σc <= rt_credit RT Σr |- _ => clear - E CRC; lia end).
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCopyInputFormat; 0x9ff88].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => agf_side PFS NFA LOR Hx).
  assert (LSUBr : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σr)) by (intros e He; rewrite LVR; apply LSUB; exact He).
  unfold hid in POD.
  lazymatch goal with PX : rw_cells asegs ?mc pixd _, PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σr _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POD2 : pix_obj (rt_live RT Σr) mc pixd (pv_res v1 v) (mkCmapv 0 0 0 0))
      by (destruct POD as (_ & CH & HOK & HD & _); rewrite LVR;
          split; [unfold pix_cells, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP; exact PX|
          split; [exact CH| split; [exact HOK| split; [exact HD| left; exact VCMAP]]]]);
    assert (POS2 : pix_obj_rc (rt_live RT Σr) mc pix v cv 1) by (exact (PSRC (rt_live RT Σr) 1 mc LSUBr AGF PS)) end.
  hide POD.
  eapply cps_seq.
  {
  eapply PCI with (lo := lo) (pixd := pixd) (pixs := pix) (vd := pv_res v1 v) (vs := v) (cvd := mkCmapv 0 0 0 0) (cvs := cv) (rc := 1).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact POD2.
  - exact POS2.
  - intros E; unfold parked in NPS; apply NPS; symmetry; exact E.
  - lenv_tac.
  }
  clear POD2 POS2.
  idtac "MARK PCI applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with E : rt_live _ _ = rt_live RT Σr |- _ => rewrite E end; apply LSUBr; exact He| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σi; rename A into ARTI end.
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
  unfold pix_cells, pv_inf, pv_res in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  assert (LVI : rt_live RT Σi = (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σi = _ |- _ => rewrite E end; rewrite LVR; exact LVC).
  assert (FRSi : rt_frames RT Σi = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σi = _ |- _ => rewrite E end; exact FRSr).
  assert (SP0i : rt_sp0 RT Σi = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRi : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σi) by (lazymatch goal with E : rt_credit RT Σr <= rt_credit RT Σi |- _ => clear - E CRr; lia end).
  assert (LSUBi : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σi)) by (intros e He; rewrite LVI; right; right; exact He).
  assert (PDINi : In (pixd, 64) (rt_live RT Σi)) by (rewrite LVI; right; left; reflexivity).
  assert (DDINi : In (dat, rs) (rt_live RT Σi)) by (rewrite LVI; left; reflexivity).
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK after PCI".
  try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixRemoveColormap; 0x9ff88].
  idtac "MARK at pixRemoveColormap".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => agf_side PFS NFA LOR Hx).
  idtac "MARK at_call PRC".
  (* [comment removed for export] *)
  pose proof UC as UCX. unfold uctx in UCX. rewrite ESP in UCX. rewrite unsigned_lit in UCX by (clear - USP0 USP1; lia).
  lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
  unfold hid in POBJ.
  lazymatch goal with PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σi _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POS3 : pix_obj_rc (rt_live RT Σi) mc pix v cv 1) by (exact (PSRC (rt_live RT Σi) 1 mc LSUBi AGF PS));
    assert (UCC : chain_ok mc (usp + -256) usp (bv_unsigned ra :: ras))
      by (apply (chain_ok_push _ (usp + -256) usp (bv_unsigned ra) (bv_unsigned s0) ras);
            [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
            | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
            | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
            | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
              split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
  hide POBJ. clear FRrec2.
  assert (CRR : REMOVE_COST <= rt_credit RT Σi) by (unfold REMOVE_COST; unfold RASTER_COST in *; clear - CRi CRB; lia).
  eapply cps_seq.
  {
  eapply PRC with (lo := lo) (pix := pix) (v := v) (cv := cv) (ras := bv_unsigned ra :: ras).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact POS3.
  - exact D8.
  - exact VDATA.
  - exact CNZ.
  - unfold uctx. rewrite !unsigned_lit by (clear - USP0 USP1 LOR STa; lia). exact UCC.
  - intros _. rewrite RAF, RAS. unfold REMOVE_RAS, RA_FUZZ_OP1, RA_TOP. rewrite unsigned_lit by (clear; lia).
    repeat (apply Forall_cons; [first [left; apply ct_mem_In; vm_compute; reflexivity | right; apply ct_mem_In; vm_compute; reflexivity] |]). apply Forall_nil.
  - lenv_tac.
  - unfold lres; rewrite FRSi, LVI; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [clear - FRB; lia| clear - LVB; lia| exact CRR| intros p n Hp; destruct Hp as [E|[E|Hp]]; [injection E; intros <- <-; exact DDN | injection E; intros <- <-; clear; lia | exact (LVP p n Hp)]].
  }
  idtac "MARK PRC applied".
  clear POS3 UCC CRR.
  after_call RT AF.
  idtac "MARK after_call PRC".
  lazymatch goal with A : ART RT ?S ?mm, D : p_cmap v = 0 /\ ?r = pix /\ _ \/ _ |- cps _ (ASTA RT ?S _ _) _ =>
    rename S into Σp; rename A into ARTP; rename mm into mp; rename r into pixt; rename D into RMC end.
  lazymatch type of RMC with _ \/ (_ /\ _ /\ pix_obj _ _ _ ?vv _ /\ _) => rename vv into vt end.
  lazymatch goal with H : p_cmap v = 0 -> rt_live RT Σp = _ |- _ => rename H into LVP0 end.
  lazymatch goal with H : p_cmap v <> 0 -> rt_live RT Σp = _ |- _ => rename H into LVP1 end.
  assert (FRSp : rt_frames RT Σp = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σp = _ |- _ => rewrite E end; exact FRSi).
  assert (SP0p : rt_sp0 RT Σp = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRp : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σp)
    by (lazymatch goal with E : rt_credit RT Σi - REMOVE_COST <= rt_credit RT Σp |- _ => unfold REMOVE_COST in E; clear - E CRi; lia end).
  fold_pres2 usp ltac:(fun Hx1 Hx2 => exact Hx2).
  idtac "MARK after PRC".
  destruct RMC as [(CM0 & EPT & PRC2)|(CMN & POSp & POT & WT & HT & DT & DATAT & CMT)].
  - (* [comment removed for export] *)
    subst pixt.
    specialize (LVP0 CM0). clear LVP1.
    assert (LVPA : rt_live RT Σp = (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVP0; exact LVI).
    assert (LSUBp : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σp)) by (intros e He; rewrite LVPA; right; right; exact He).
    assert (PDINp : In (pixd, 64) (rt_live RT Σp)) by (rewrite LVPA; right; left; reflexivity).
    assert (DDINp : In (dat, rs) (rt_live RT Σp)) by (rewrite LVPA; left; reflexivity).
    assert (PINp : In (pix, 64) (rt_live RT Σp)) by (apply LSUBp; exact PIN).
    assert (DINp : In (p_data v, 4 * (p_wpl v * p_h v)) (rt_live RT Σp)) by (apply LSUBp; exact DIN).
    pose proof PRC2 as (PXS & _). unfold pix_cells_rc in PXS.
    hide PRC2.
    assert (EWS : p_wpl v = (p_w v * 8 + 31) / 32) by (rewrite HWPL, D8; reflexivity).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK arm A start".
    try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
    walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9f804].
    (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _, A : ART RT _ ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => agf_side PFS NFA LOR Hx) end.
    lazymatch goal with A : ART RT Σp ?mm |- cps _ (ASTA RT Σp _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename A into ARTj; rename mm into mj end.
    idtac "MARK arm A junction art".
    (* [comment removed for export] *)
    rewrite ESP.
    assert (WPLS : 0 < p_wpl v <= 5001) by (rewrite EWS; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    assert (WPLD : 0 < p_wpl v1 <= 1251) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    rewrite !(sx32_small (p_wpl v)) by (clear - WPLS; lia).
    rewrite (sx32_small (p_wpl v1)) in FR by (clear - WPLD; lia).
    (* [comment removed for export] *)
    pose proof FR as T. split_at T (if (0 =? 0)%Z then 3%nat else 4%nat) C48. split_at C48 1%nat FRBLK.   (* [comment removed for export] *) split_at FRBLK 8%nat T3.
    lazymatch type of T3 with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in split_at T3 n UREC end. clear T T3.
    rewrite <- (Z_to_bv_bv_unsigned s0) in UREC. rewrite <- (Z_to_bv_bv_unsigned ra), RAF in UREC.
    assert (WLO : wr_at asegs mj (usp + -256 + 16) 24) by (apply (wr_at_sub mj (usp + -256) 256 (usp + -256 + 16) 24 (rw_cells_wr_at _ _ _ _ 256 FR ltac:(cbn; clear; lia))); clear; lia).
    (* [comment removed for export] *)
    pose proof FRM as T. split_at T 4%nat FW. split_at FW 1%nat T2. clear T T2. rewrite (sx32_small (p_w v)) in FW by (clear - HW0 HW2; lia).
    pose proof FRM as T. split_at T 6%nat FH. split_at FH 1%nat T2. clear T T2. rewrite (sx32_small (p_h v)) in FH by (clear - HH0 HH2; lia).
    pose proof FRM as T. split_at T 12%nat FPD. split_at FPD 1%nat T2. clear T T2.
    (* [comment removed for export] *)
    set (vd := mkPixv (p_w v) (p_h v) 2 (p_spp v1) (p_wpl v1) (p_xres v) (p_yres v) (p_inf v) (p_spec v1) 0 dat).
    assert (PODj : pix_obj (rt_live RT Σp) mj pixd vd (mkCmapv 0 0 0 0)).
    { unfold hid in HOKD. split; [unfold pix_cells, vd; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXD|].
      split; [split; [exact PDINp| split; [exact PD0| split; [exact PD16| clear; lia]]]|].
      split; [unfold pix_hdr_ok in HOKD |- *; unfold vd; cbn [p_w p_h p_d p_wpl]; rewrite VW, VH, VD in HOKD; exact HOKD|].
      split; [right; unfold vd, rsize; cbn [p_data p_wpl p_h]; split; [split; [rewrite <- VH; exact DDINp| split; [exact DD0| split; [exact DD16| rewrite <- VH; exact DDN]]]| unpark DDNE; exact DDNE]|].
      left; reflexivity. }
    assert (GEOM : d2m_geom (rt_sp0 RT Σp) lo (usp + -256) usp fr pixd dat rs (p_data v) (4 * (p_wpl v * p_h v)) (p_wpl v) (p_wpl v1) (p_w v) (p_h v)).
    { unfold d2m_geom. rewrite SP0p. unfold STACK_WIN, SEGTOP_A, USTACK_TOP, LSTK, RT_STACK.
      unpark CKS2; unpark CKH2; unpark CKS0; unpark CKH0; unpark CKS1; unpark CKH1; unpark DRD; unpark DPD; unpark DRP; unpark FRSH; unpark FCD0; unpark FCD1; unpark FCD2.
      clear - HW0 HW2 HH0 HH2 EWS EWD ERS VH HRS1 DD0 DD16 CKR2 CKS2 CKH2 D0 D16 CKR0 CKS0 CKH0 PD0 PD16 CKR1 CKS1 CKH1 DRD DPD DRP FR0 FR64 FRHI FRSEG FRSH FCD0 FCD1 FCD2 LOW STa LOR AL SPA SPT SPB SP0R0 SP0R1 SP0W.
      repeat lazymatch goal with |- _ /\ _ => split end; first [assumption | lia | rewrite ERS, VH; reflexivity | idtac]. }
    idtac "MARK arm A junction facts".
    assert (PFU : forall a, usp <= a < 140737488355328 -> PF a).
    { intros a Ha. unfold PF. split; [left; unfold USTACK_TOP; clear - Ha; lia| cbn [outside]; clear - Ha CKR LOW LOR; lia]. }
    assert (UCXj : chain_ok mj usp (bv_unsigned s0) [RA_TOP]).
    { rewrite <- RAS. apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX). eapply agree_sub; [exact AGF|]. cbv beta. intros zx Hzx. apply PFU. unfold USTACK_TOP in Hzx. clear - Hzx. lia. }
    assert (FP1R : 0 <= bv_unsigned s0 < 2^64) by (pose proof (bv_unsigned_in_range 64 s0) as X; unfold bv_modulus in X; change (2 ^ Z.of_N 64) with (2^64) in X; exact X).
    eapply cps_seq.
    { eapply (d2_mid RT AF GP RC CML SCM CMF) with (lo := lo) (sa := usp + -256) (usp := usp) (fr := fr) (pixd := pixd) (dat := dat) (rd := rs) (datas := p_data v)
         (rs := 4 * (p_wpl v * p_h v)) (wpls := p_wpl v) (wpld := p_wpl v1) (w := p_w v) (h := p_h v) (fp1 := bv_unsigned s0) (vd := vd) (frs0 := rt_frames RT Σ).
      all: lazymatch goal with
       | |- fdfs_only _ => exact FDO
       | |- mat_stable _ => exact MST
       | |- d2m_geom _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact GEOM
       | |- pix_obj _ _ _ _ _ => exact PODj
       | |- In _ (rt_live _ _) => exact DINp
       | |- rt_frames _ _ = _ => exact FRSp
       | |- chain_ok _ _ _ _ => exact UCXj
       | |- ART _ _ _ => exact ARTj
       | |- wr_at _ _ _ _ => exact WLO
       | |- rw_cells _ _ ?A (CB 8 _ :: _) => lazymatch type of FRBLK with rw_cells _ _ ?B _ => replace A with B by (clear; lia) end; exact FRBLK
       | |- rw_cells _ ?mm ?A ?cs => first [ assumption | match goal with H : rw_cells _ mm ?B cs |- _ => replace A with B by (clear; lia); exact H end | idtac "LEFT-cells" A ]
       | |- Z.of_nat (length (rt_live _ _)) + _ <= _ => rewrite LVPA; cbn [length]; clear - LVB; unfold LIVE_MAX in *; lia
       | |- Z.of_nat (length (rt_frames _ _)) + _ <= _ => rewrite FRSp; cbn [length]; clear - FRB; unfold FRAMES_MAX in *; lia
       | |- _ <= rt_credit _ _ => clear - CRp CRB; unfold RASTER_COST in *; lia
       | |- forall p n, In (p, n) _ -> 0 < n => intros p n Hp; rewrite LVPA in Hp; cbn [In] in Hp; destruct Hp as [E|[E|Hp]]; [injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| exact (LVP p n Hp)]
       | |- 0 <= bv_unsigned _ < _ => exact FP1R
       | |- _ => first [assumption | reflexivity | lazymatch goal with |- ?g => idtac "MID SIDE LEFT:" g end]
       end. }
    idtac "MARK arm A mid applied".
    clear PODj GEOM WLO UCXj FP1R C48 FRBLK UREC FW FH FPD.
    hide FR. hide FRM. hide FSH. hide PXS. clear PXD.
    after_call RT AF.
    idtac "MARK arm A after mid".
    Show.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σm; rename A into ARTM; rename mm into mmid end.
    lazymatch goal with H : rt_live RT Σm = (?ca, 16) :: (?cm, 24) :: rt_live RT Σp |- _ => rename H into LVMN; rename ca into carr; rename cm into cmap end.
    lazymatch goal with H : cmap_obj _ mmid cmap _ |- _ => rename H into CMO end.
    lazymatch goal with H : rw_cells asegs mmid pixd (pix_cells _) |- _ => rename H into PXD end.
    lazymatch goal with H : rw_cells asegs mmid (usp + -256 + 24) _ |- _ => rename H into S24 end.
    lazymatch goal with H : agree_on (d2m_keep _ _ _ _ _ _) mj mmid |- _ => rename H into AGM end.
    lazymatch goal with H : forall e, In e (rt_live RT Σp) -> fst e <> cmap /\ fst e <> carr |- _ => rename H into FZ end.
    lazymatch goal with H : forall a, d2m_keep _ _ _ _ _ _ a -> _ /\ _ |- _ => rename H into NCX end.
    assert (LVM : rt_live RT Σm = (carr, 16) :: (cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVMN, LVPA; reflexivity).
    assert (FRSm : rt_frames RT Σm = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σm = _ |- _ => rewrite E end; exact FRSp).
    assert (SP0m : rt_sp0 RT Σm = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σm = _ |- _ => rewrite E end; first [reflexivity | exact SP0p]).
    assert (CRm : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σm) by (lazymatch goal with E : rt_credit RT Σp - 6 <= rt_credit RT Σm |- _ => clear - E CRp; lia end).
    assert (LSUBm : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σm)) by (intros e He; rewrite LVM; do 4 right; exact He).
    pose proof CMO as ((cpad & CMC) & (KMIN & KM0 & KM16 & _) & (KAIN & KA0 & KA16 & _) & KOK & KANE).
    unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC, KAIN, KA0, KA16, KANE.
    destruct (FZ _ PDINp) as [NCMP NCAP]. destruct (FZ _ DDINp) as [NCMD NCAD]. destruct (FZ _ PINp) as [NCMX NCAX]. destruct (FZ _ DINp) as [NCMS NCAS].
    cbn [fst] in NCMP, NCAP, NCMD, NCAD, NCMX, NCAX, NCMS, NCAS.
    idtac "MARK arm A mid names".
    (* [comment removed for export] *)
    unfold hid in FR.
    (* [comment removed for export] *)
    pose proof FR as P0. split_at P0 1%nat T.
    tryif constr_eq (0)%Z 0%Z then (split_at T 1%nat T40; split_last_CB T [8%nat; 24%nat]; split_at T 1%nat Tw; clear Tw; rename T into P8)
                                 else (split_at T 2%nat T40; clear T).
    split_at T40 2%nat Tm. split_at Tm 8%nat P144. clear Tm FR.
    unfold d2m_keep, d2m_W in AGM.
    carry AGM P0 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR1 CKR2 LOW LOR; repeat split; try exact I; lia).
    try (carry AGM P8 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR1 CKR2 LOW LOR; repeat split; try exact I; lia)).
    carry AGM T40 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR1 CKR2 LOW LOR; repeat split; try exact I; lia).
    carry AGM P144 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR1 CKR2 LOW LOR; repeat split; try exact I; lia).
    carry AGM FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [rewrite FRSp; left; reflexivity| change (fs_size 2%nat) with 256; clear - Hx; lia])
                  ltac:(fun Hx => unpark FCD1; unpark FCD2; clear - Hx FCD1 FCD2 FRHI LOW LOR; repeat split; try exact I; lia).
    carry AGM FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [rewrite FRSp; left; reflexivity| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia])
                  ltac:(fun Hx => unpark FCS1; unpark FCS2; unfold shad, SHB in *; clear - Hx FCS1 FCS2 FR64 FRHI SP0R1 SP0W LOW LOR; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    carry AGM PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [exact PINp| exact Hx])
                  ltac:(fun Hx => unpark DSD; unpark DSP; clear - Hx DSD DSP CKR LOW LOR; repeat split; try exact I; lia).
    idtac "MARK arm A carried m".
    fold_ag ltac:(fun Hx => pose proof (PFS _ Hx) as P1; pose proof (NCD _ Hx) as N1; pose proof (NCP _ Hx) as N2; destruct Hx as [Hx1 Hx2]; split;
                   [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [exact LSUBp| intros e He; rewrite FRSp; right; exact He| clear; lia]
                   | cbn [outside]; clear - P1 N1 N2 LOR; repeat split; try exact I; lia]).
    idtac "MARK arm A folded m".
    (* [comment removed for export] *)
    sigma_gc RT Σ Σm.
    assert (CMINm : In (cmap, 24) (rt_live RT Σm)) by (rewrite LVM; right; left; reflexivity).
    assert (CAINm : In (carr, 16) (rt_live RT Σm)) by (rewrite LVM; left; reflexivity).
    assert (PDINm : In (pixd, 64) (rt_live RT Σm)) by (rewrite LVM; do 3 right; left; reflexivity).
    assert (DDINm : In (dat, rs) (rt_live RT Σm)) by (rewrite LVM; do 2 right; left; reflexivity).
    assert (PINm : In (pix, 64) (rt_live RT Σm)) by (apply LSUBm; exact PIN).
    assert (DINm : In (p_data v, 4 * (p_wpl v * p_h v)) (rt_live RT Σm)) by (apply LSUBm; exact DIN).
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    chunk_facts RT AF GP cmap 24. chunk_facts RT AF GP carr 16.
    fframe_chunk RT AF fr 2%nat 256 cmap 24. fframe_chunk RT AF fr 2%nat 256 carr 16.
    pose proof (live_apart2 RT AF Σm _ cmap 24 pix 64 ARTM CMINm PINm ltac:(intros E; injection E as E1 _; exact (NCMX (eq_sym E1)))) as ACMX.
    pose proof (live_apart2 RT AF Σm _ cmap 24 pixd 64 ARTM CMINm PDINm ltac:(intros E; injection E as E1 _; exact (NCMP (eq_sym E1)))) as ACMP.
    park_disj. park_ne.
    idtac "MARK arm A cm facts".
    (* [comment removed for export] *)
    lazymatch goal with WW1 : wr_at asegs ?mc (usp + -256 + 16) 24, WW2 : wr_at asegs ?mc (usp + -256 + 56) 88 |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      destruct (wr_at_rw_CB mc (usp + -256 + 16) 8 (wr_at_sub mc (usp + -256 + 16) 24 (usp + -256 + 16) 8 WW1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as [j16 P16];
      destruct (wr_at_rw_CB mc (usp + -256 + 32) 8 (wr_at_sub mc (usp + -256 + 16) 24 (usp + -256 + 32) 8 WW1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as [j32 P32];
      destruct (wr_at_rw_CB mc (usp + -256 + 56) 88 WW2 ltac:(clear; lia)) as [j56 P56]; clear WW1 WW2 end.
    change (Z.to_nat 8) with 8%nat in P16, P32. change (Z.to_nat 88) with 88%nat in P56.
    try (join_cells P0 P8). join_cells P0 P16. join_cells P0 S24. join_cells P0 P32. join_cells P0 T40. join_cells P0 P56. join_cells P0 P144.
    rename P0 into FR.
    idtac "MARK arm A FR rebuilt".
    (* [comment removed for export] *)
    try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
    walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDestroy].
    idtac "MARK arm A at pixDestroy".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    (* [comment removed for export] *)
    split_at FRM 10%nat PPC. split_at PPC 1%nat FRMb.
    pose proof FSH as SH10. split_at SH10 10%nat SH10b. split_at SH10b 1%nat SH10c. clear SH10 SH10c.
    lazymatch goal with PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σm _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (POS4 : pix_obj_rc (rt_live RT Σm) mc pix v cv 2) by (exact (PSRC (rt_live RT Σm) 2 mc LSUBm AGF PS));
      assert (OPP : optrL RT (rt_live RT Σm) Σm mc (fr + 80) 8)
        by (unfold optrL, accok; split;
            [ right; exists fr, 2%nat; rewrite FRSm; change (fs_size 2) with 256;
              split; [left; reflexivity|]; split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FR0; lia|];
              split; [clear - FRHI SP0R1; lia|];
              replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
              destruct SH10b as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B
            | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; unfold SEGTOP_A; split; [unpark FRSH; clear - FRSH; lia| clear - FRSEG; lia] ]) end.
    idtac "MARK arm A destroy args".
    assert (CR1 : 1 <= rt_credit RT Σm) by (clear - CRm CRB; unfold RASTER_COST in *; lia).
    eapply cps_seq.
    { eapply PDR with (lo := lo) (pp := fr + 80) (pix := pix) (v := v) (cv := cv) (rc := 2).
      - exact FDO.
      - exact MST.
      - reflexivity.
      - reflexivity.
      - exact OPP.
      - exact PPC.
      - exact POS4.
      - clear; lia.
      - unpark FCD; clear - FCD; lia.
      - lenv_tac.
      - unfold lres; rewrite FRSm, LVM; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [clear - FRB; lia| clear - LVB; lia| exact CR1|
          intros p n Hp; destruct Hp as [E|[E|[E|[E|Hp]]]]; [injection E; intros <- <-; clear; lia| injection E; intros <- <-; clear; lia| injection E; intros <- <-; exact DDN
            | injection E; intros <- <-; clear; lia | exact (LVP p n Hp)]]. }
    idtac "MARK arm A PDR applied".
    clear POS4 OPP CR1 SH10b.
    hide FRM. hide FRMb. hide FSH. hide PXD. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σz; rename A into ARTZ end.
    assert (LVZ : rt_live RT Σz = (carr, 16) :: (cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σz = _ |- _ => rewrite E end; exact LVM).
    assert (FRSz : rt_frames RT Σz = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σz = _ |- _ => rewrite E end; exact FRSm).
    assert (SP0z : rt_sp0 RT Σz = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; first [reflexivity | exact SP0m]).
    assert (CRz : rt_credit RT Σ - (2 * RASTER_COST + 32) <= rt_credit RT Σz) by (lazymatch goal with E : rt_credit RT Σm - 1 <= rt_credit RT Σz |- _ => clear - E CRm; lia end).
    assert (LSUBz : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σz)) by (intros e He; rewrite LVZ; do 4 right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => unpark FCD; clear - Hx FCD; lia);
      carry AGx FRMb ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => unpark FCD; clear - Hx FCD; lia);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia])
                    ltac:(fun Hx => unpark FCS; unpark FRSH; unfold shad, SHB in *; clear - Hx FCS FR64 FRSH CKH; first [lia | Z.div_mod_to_equations; lia]);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [rewrite LVZ; do 3 right; left; reflexivity| exact Hx]) ltac:(fun Hx => unpark DSP; repeat match goal with H : parked (fr + 256 <= pixd \/ _ <= fr) |- _ => unpark H; revert H end; clear - Hx DSP; intros; cbn [outside]; repeat split; try exact I; lia);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [rewrite LVZ; right; left; reflexivity| exact Hx]) ltac:(fun Hx => unpark ACMX; repeat match goal with H : parked (fr + 256 <= cmap \/ _ <= fr) |- _ => unpark H; revert H end; clear - Hx ACMX; intros; cbn [outside]; repeat split; try exact I; lia) end.
    idtac "MARK arm A carried z".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; cbn [outside] in Hx2; destruct (NFA _ (conj Hx1 Hx2)) as [N1 N2]; clear - N1 Hx2; repeat split; try exact I; lia).
    lazymatch goal with H : rw_cells asegs _ pix (pix_cells_rc v (2 - 1)) |- _ => rename H into PXS end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK arm A after destroy".
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT Σz ?mm |- _ => rename mm into mz end.
    assert (FZP : forall e, In e (rt_live RT Σ) -> fst e <> pixd) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(carr, 16); (cmap, 24); (dat, rs)] pixd 64 (rt_live RT Σ) e ARTZ); [rewrite LVZ; reflexivity| cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [q k]; exact (LVP q k He)]).
    assert (FZD : forall e, In e (rt_live RT Σ) -> fst e <> dat) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(carr, 16); (cmap, 24)] dat rs ((pixd, 64) :: rt_live RT Σ) e ARTZ); [rewrite LVZ; reflexivity| cbn [app In]; do 3 right; exact He| exact DDN| destruct e as [q k]; exact (LVP q k He)]).
    assert (FZC : forall e, In e (rt_live RT Σ) -> fst e <> cmap) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(carr, 16)] cmap 24 ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) e ARTZ); [rewrite LVZ; reflexivity| cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [q k]; exact (LVP q k He)]).
    assert (FZA : forall e, In e (rt_live RT Σ) -> fst e <> carr) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [] carr 16 ((cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) e ARTZ); [rewrite LVZ; reflexivity| cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [q k]; exact (LVP q k He)]).
    assert (PDINz : In (pixd, 64) (rt_live RT Σz)) by (rewrite LVZ; do 3 right; left; reflexivity).
    assert (DDINz : In (dat, rs) (rt_live RT Σz)) by (rewrite LVZ; do 2 right; left; reflexivity).
    assert (CMINz : In (cmap, 24) (rt_live RT Σz)) by (rewrite LVZ; right; left; reflexivity).
    assert (CAINz : In (carr, 16) (rt_live RT Σz)) by (rewrite LVZ; left; reflexivity).
    assert (PINz : In (pix, 64) (rt_live RT Σz)) by (apply LSUBz; exact PIN).
    assert (DINz : In (p_data v, 4 * (p_wpl v * p_h v)) (rt_live RT Σz)) by (apply LSUBz; exact DIN).
    sigma_gc RT Σ Σz.
    repeat match goal with H : In (?b, _) (rt_live RT Σ) |- _ => lazymatch b with pix => fail | p_data v => fail | _ => clear H end end.
    idtac "MARK arm A diet".
    hide PXS. hide PXD. hide CMC.
    try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0xa0020].
    idtac "MARK arm A at flag load".
    idtac "MARK arm A at pokes".
    try unfold hid in FRM. try unfold hid in FSH. split_at FRM 1%nat FRMr.
    Time (eapply evt_cut;
    [ eapply EVQ_exit;
      [ eapply d2bpp_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
      | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
    | ]).
    clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold d2bpp_exit_W, SHB in MUx. unfold d2bpp_sh_f5 in FSH.
    idtac "MARK arm A pokes applied".
    Time loop_art RT AF Σz mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    Time (lazymatch type of MUx with munch _ ?ma ?mb =>
      loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *;
          first [pose proof FRSEG as XFRSEG | pose proof I as XFRSEG]; first [pose proof SP0W as XSP0W | pose proof I as XSP0W]; first [pose proof FRSH as XFRSH | pose proof I as XFRSH];
          clear - Hx FRHI LOW LOR FR64 FR0 SP0R1 SP0R0 XFRSEG XSP0W XFRSH;
          unfold parked, hid in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end).
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => chunk_side fr pix FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx);
      carry_mu MUx PXD ltac:(fun Hx => chunk_side fr pixd FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx);
      carry_mu MUx CMC ltac:(fun Hx => chunk_side fr cmap FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx) end.
    hide PXS. hide PXD. hide CMC.
    join_cells FRM FRMr.
    idtac "MARK arm A carried x".
    frame_release_g RT AF GP MST Σ fr 2%nat 256 PF AGF PFS usp lo 0xa00d4
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => agf_side PFS NFA LOR Hx) ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
    idtac "MARK arm A frame released".
    lazymatch goal with MUx : munch [(?fl, ?fl + 1)] _ ?mb |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => repeat match goal with Hf : fl < pix \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx PXD ltac:(fun Hx => repeat match goal with Hf : fl < pixd \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx CMC ltac:(fun Hx => repeat match goal with Hf : fl < cmap \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia) end.
    hide PXS. hide PXD. hide CMC.
    clear_acc. refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
    walk_to AF MST [(usp - 256, usp)] (@nil Z).
    lazymatch goal with MUx : munch _ _ ?mb |- evt _ _ (MS _ _ _ _ _ ?mb _) =>
      carry_mu MUx PXS ltac:(fun Hx => chunk_side fr pix FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx);
      carry_mu MUx PXD ltac:(fun Hx => chunk_side fr pixd FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx);
      carry_mu MUx CMC ltac:(fun Hx => chunk_side fr cmap FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx) end.
    cps_stop.
    idtac "MARK arm A epilogue walked".
    (* [comment removed for export] *)
    apply cps_finish; intros c Hc; subst QF; unfold d2bpp_post; cbv beta.
    set (vf := mkPixv (p_w v) (p_h v) 2 (p_spp v1) (p_wpl v1) (p_xres v) (p_yres v) (p_inf v) (p_spec v1) cmap dat).
    unfold hid in HOKD, PXS, PXD, CMC.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, pixd, vf, (mkCmapv carr 2 4 4) end.
    split.
    2: {
    split; [intros Z0; exfalso; clear - Z0 PD0; lia|].
    split.
    { intros _. rewrite LV2, LVZ.
      unpark VDATA1; unpark DDNE; unpark NCMP; unpark NCAP; unpark NCMD; unpark NCAD; unpark KANE.
      apply (live_destroy_d2 (rt_live RT Σ) pixd dat rs cmap carr 16 vf (mkCmapv carr 2 4 4));
        [reflexivity| reflexivity| reflexivity| exact VDATA1| clear - KM0; lia| clear - KA0; lia
        | exact DDNE| exact NCAD| exact NCMD| intro E; apply NCAP; symmetry; exact E| intro E; apply NCMP; symmetry; exact E| intro E; apply KANE; symmetry; exact E
        | exact FZP| exact FZD| exact FZC| exact FZA]. }
    split.
    { intros p n Hp. rewrite LV2, LVZ in Hp. cbn [In] in Hp.
      destruct Hp as [E|[E|[E|[E|Hp]]]]; [injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| exact (LVP p n Hp)]. }
    split; [rewrite LV2, LVZ; cbn [length]; clear; lia|].
    split; [rewrite FRS2; first [reflexivity | exact FRSz]|]. split; [rewrite SP2; first [exact SP0z | reflexivity]|].
    unfold D2_COST, OP_COST, is_d8. cbn [Z.eqb Pos.eqb]. rewrite CR2. clear - CRz. unfold RASTER_COST in *. lia.
    }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    split; [unfold lpost_f, rt_after_f; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); split; [split; [assumption| split; assumption]| split; assumption]|].
    split; [unfold keepsL, rt_pres_fp; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
    split.
    { rewrite LV2, LVZ. lazymatch goal with PS : rw_cells asegs ?mc pix _ |- pix_obj _ ?mc _ _ _ =>
        exact (PSRC ((carr, 16) :: (cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) 1 mc ltac:(intros e He; do 4 right; exact He) AGF PS) end. }
    right. split; [| cbn [p_data]; unpark VDATA1; exact VDATA1].
    rewrite LV2, LVZ.
    split; [unfold pix_cells, vf; unfold vd in PXD; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD |- *; exact PXD|].
    split; [split; [do 3 right; left; reflexivity| split; [exact PD0| split; [exact PD16| clear; lia]]]|].
    split; [unfold pix_hdr_ok in HOKD |- *; unfold vf; cbn [p_w p_h p_d p_wpl]; rewrite VW, VH, VD in HOKD; exact HOKD|].
    split; [right; unfold vf, rsize; cbn [p_data p_wpl p_h]; split; [split; [do 2 right; left; rewrite <- VH; reflexivity| split; [exact DD0| split; [exact DD16| rewrite <- VH; exact DDN]]]| unpark DDNE; exact DDNE]|].
    right. unfold vf; cbn [p_cmap p_data c_arr].
    split.
    { split; [exists cpad; unfold cmap_cells; cbn [c_arr c_depth c_nalloc c_n]; exact CMC|].
      split; [split; [right; left; reflexivity| split; [exact KM0| split; [exact KM16| clear; lia]]]|].
      split; [cbn [c_arr c_nalloc]; split; [left; reflexivity| split; [exact KA0| split; [exact KA16| clear; lia]]]|].
      split; [exact KOK| cbn [c_arr]; unpark KANE; exact KANE]. }
    unpark NCMP; unpark NCAP; unpark NCMD; unpark NCAD.
    repeat split; intro E; [apply NCMP | apply NCAP | apply NCMD | apply NCAD]; symmetry; exact E.
  - (* [comment removed for export] *)
    specialize (LVP1 CMN). clear LVP0.
    set (dtt := p_data vt) in *. set (rst := rsize vt) in *.
    assert (LVPB : rt_live RT Σp = (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVP1, LVI; reflexivity).
    assert (LSUBp : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σp)) by (intros e He; rewrite LVPB; do 4 right; exact He).
    pose proof POT as (PXT & (PTIN & PT0 & PT16 & _) & HOKT & PTDATA & _).
    destruct PTDATA as [PTZ|((DTIN & DT0 & DT16 & DTN) & DTNE)]; [exfalso; exact (DATAT PTZ)|].
    fold dtt in DTIN, DTN, DTNE, DT0, DT16. fold rst in DTIN, DTN.
    unfold pix_cells in PXT. rewrite WT, HT, DT, CMT in PXT. fold dtt in PXT.
    pose proof POSp as (PXS & _). unfold pix_cells in PXS.
    assert (EWS : p_wpl vt = (p_w v * 8 + 31) / 32) by (destruct HOKT as (_ & _ & _ & Q4 & _); rewrite WT, DT in Q4; exact Q4).
    assert (ERST : rst = 4 * (p_wpl vt * p_h v)) by (unfold rst, rsize; rewrite HT; reflexivity).
    assert (RSTB : 0 < 4 * (p_wpl vt * p_h v) <= 67108864) by (destruct HOKT as (_ & _ & _ & _ & Q5); rewrite HT in Q5; exact Q5).
    (* [comment removed for export] *)
    assert (SUBT : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> In e (rt_live RT Σp) /\ fst e <> pixt)
      by (intros e He; split; [rewrite LVPB; right; right; exact He|];
          apply (fresh_chunk_ne RT AF Σp _ [(dtt, rst)] pixt 64 _ e ARTP LVPB); [ cbn [app]; right; exact He | clear; lia
          | destruct He as [<-|[<-|He]]; [exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)] ]).
    assert (SUBDT : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> In e (rt_live RT Σp) /\ fst e <> dtt)
      by (intros e He; split; [rewrite LVPB; right; right; exact He|];
          apply (fresh_chunk_ne RT AF Σp _ [] dtt rst _ e ARTP LVPB); [ cbn [app]; right; exact He | exact DTN
          | destruct He as [<-|[<-|He]]; [exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)] ]).
    assert (NST : pix <> pixt) by (exact (proj2 (SUBT (pix, 64) ltac:(right; right; exact PIN)))).
    assert (NSDT : pix <> dtt) by (exact (proj2 (SUBDT (pix, 64) ltac:(right; right; exact PIN)))).
    assert (NPT : pixd <> pixt) by (exact (proj2 (SUBT (pixd, 64) ltac:(right; left; reflexivity)))).
    assert (NPDT : pixd <> dtt) by (exact (proj2 (SUBDT (pixd, 64) ltac:(right; left; reflexivity)))).
    assert (NDT : dat <> pixt) by (exact (proj2 (SUBT (dat, rs) ltac:(left; reflexivity)))).
    assert (NDDT : dat <> dtt) by (exact (proj2 (SUBDT (dat, rs) ltac:(left; reflexivity)))).
    assert (NRT : p_data v <> pixt) by (exact (proj2 (SUBT (p_data v, 4 * (p_wpl v * p_h v)) ltac:(right; right; exact DIN)))).
    assert (NRDT : p_data v <> dtt) by (exact (proj2 (SUBDT (p_data v, 4 * (p_wpl v * p_h v)) ltac:(right; right; exact DIN)))).
    assert (PINp : In (pix, 64) (rt_live RT Σp)) by (apply LSUBp; exact PIN).
    assert (DINp : In (p_data v, 4 * (p_wpl v * p_h v)) (rt_live RT Σp)) by (apply LSUBp; exact DIN).
    assert (PDINp : In (pixd, 64) (rt_live RT Σp)) by (rewrite LVPB; do 3 right; left; reflexivity).
    assert (DDINp : In (dat, rs) (rt_live RT Σp)) by (rewrite LVPB; do 2 right; left; reflexivity).
    chunk_facts RT AF GP pixt 64. chunk_facts RT AF GP dtt rst.
    fframe_chunk RT AF fr 2%nat 256 pixt 64. fframe_chunk RT AF fr 2%nat 256 dtt rst.
    lazymatch goal with A : ART RT Σp ?mm |- _ =>
      pose proof (live_apart2 RT AF Σp mm pix 64 pixt 64 A PINp PTIN ltac:(intros E; injection E; intros E1; exact (NST E1))) as DSXT;
      pose proof (live_apart2 RT AF Σp mm pix 64 dtt rst A PINp DTIN ltac:(intros E; injection E; intros _ E1; exact (NSDT E1))) as DSDT;
      pose proof (live_apart2 RT AF Σp mm pixd 64 pixt 64 A PDINp PTIN ltac:(intros E; injection E; intros E1; exact (NPT E1))) as DPXT;
      pose proof (live_apart2 RT AF Σp mm pixd 64 dtt rst A PDINp DTIN ltac:(intros E; injection E; intros _ E1; exact (NPDT E1))) as DPDT;
      pose proof (live_apart2 RT AF Σp mm dat rs dtt rst A DDINp DTIN ltac:(intros E; injection E; intros _ E1; exact (NDDT E1))) as DDDT;
      pose proof (live_apart2 RT AF Σp mm pixt 64 dtt rst A PTIN DTIN ltac:(intros E; injection E; intros _ E1; unfold parked in DTNE; exact (DTNE (eq_sym E1)))) as DTT end.
    hide POT. hide POSp. hide HOKT. hide SUBT. hide SUBDT.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK arm B start".
    try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
    walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9f804].
    idtac "MARK arm B at mid".
    (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _, A : ART RT _ ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => agf_side PFS NFA LOR Hx) end.
    lazymatch goal with A : ART RT Σp ?mm |- cps _ (ASTA RT Σp _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename A into ARTj; rename mm into mj end.
    idtac "MARK arm B junction art".
    (* [comment removed for export] *)
    rewrite ESP.
    assert (WPLS : 0 < p_wpl vt <= 5001) by (rewrite EWS; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    assert (WPLD : 0 < p_wpl v1 <= 1251) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    rewrite !(sx32_small (p_wpl vt)) by (clear - WPLS; lia).
    rewrite (sx32_small (p_wpl v1)) in FR by (clear - WPLD; lia).
    (* [comment removed for export] *)
    pose proof FR as T. split_at T (if (0 =? 0)%Z then 3%nat else 4%nat) C48. split_at C48 1%nat FRBLK.   (* [comment removed for export] *) split_at FRBLK 8%nat T3.
    lazymatch type of T3 with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in split_at T3 n UREC end. clear T T3.
    rewrite <- (Z_to_bv_bv_unsigned s0) in UREC. rewrite <- (Z_to_bv_bv_unsigned ra), RAF in UREC.
    assert (WLO : wr_at asegs mj (usp + -256 + 16) 24) by (apply (wr_at_sub mj (usp + -256) 256 (usp + -256 + 16) 24 (rw_cells_wr_at _ _ _ _ 256 FR ltac:(cbn; clear; lia))); clear; lia).
    (* [comment removed for export] *)
    pose proof FRM as T. split_at T 4%nat FW. split_at FW 1%nat T2. clear T T2. rewrite (sx32_small (p_w v)) in FW by (clear - HW0 HW2; lia).
    pose proof FRM as T. split_at T 6%nat FH. split_at FH 1%nat T2. clear T T2. rewrite (sx32_small (p_h v)) in FH by (clear - HH0 HH2; lia).
    pose proof FRM as T. split_at T 12%nat FPD. split_at FPD 1%nat T2. clear T T2.
    (* [comment removed for export] *)
    set (vd := mkPixv (p_w v) (p_h v) 2 (p_spp v1) (p_wpl v1) (p_xres v) (p_yres v) (p_inf v) (p_spec v1) 0 dat).
    assert (PODj : pix_obj (rt_live RT Σp) mj pixd vd (mkCmapv 0 0 0 0)).
    { unfold hid in HOKD. split; [unfold pix_cells, vd; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PXD|].
      split; [split; [exact PDINp| split; [exact PD0| split; [exact PD16| clear; lia]]]|].
      split; [unfold pix_hdr_ok in HOKD |- *; unfold vd; cbn [p_w p_h p_d p_wpl]; rewrite VW, VH, VD in HOKD; exact HOKD|].
      split; [right; unfold vd, rsize; cbn [p_data p_wpl p_h]; split; [split; [rewrite <- VH; exact DDINp| split; [exact DD0| split; [exact DD16| rewrite <- VH; exact DDN]]]| unpark DDNE; exact DDNE]|].
      left; reflexivity. }
    assert (GEOM : d2m_geom (rt_sp0 RT Σp) lo (usp + -256) usp fr pixd dat rs dtt rst (p_wpl vt) (p_wpl v1) (p_w v) (p_h v)).
    { unfold d2m_geom. rewrite SP0p. unfold STACK_WIN, SEGTOP_A, USTACK_TOP, LSTK, RT_STACK.
      unpark CKS2; unpark CKH2; unpark CKS1; unpark CKH1; unpark DPD; unpark FRSH; unpark FCD1; unpark FCD2.
      repeat match goal with H : parked (?a + _ <= dtt \/ dtt + rst <= ?a) |- _ => unpark H end.
      repeat match goal with H : parked (dtt + rst <= _ \/ _ <= dtt) |- _ => unpark H end.
      repeat match goal with H : parked (fr + 256 <= dtt \/ _ <= fr) |- _ => unpark H end.
      repeat match goal with H : dtt + rst <= rt_sp0 RT Σ - _ |- _ => revert H end.
      repeat match goal with H : dtt + rst <= 65536 \/ _ <= dtt |- _ => revert H end.
      repeat match goal with H : dtt + rst <= 2147446784 \/ _ <= dtt |- _ => revert H end.
      repeat match goal with H : fr + 256 <= dtt \/ dtt + rst <= fr |- _ => revert H end.
      revert DPDT DDDT.
      clear - HW0 HW2 HH0 HH2 EWS EWD ERS ERST RSTB VH DD0 DD16 CKR2 CKS2 CKH2 DT0 DT16 PD0 PD16 CKR1 CKS1 CKH1 DPD FR0 FR64 FRHI FRSEG FRSH FCD1 FCD2 LOW STa LOR AL SPA SPT SPB SP0R0 SP0R1 SP0W.
      intros; unfold parked in *;
      repeat lazymatch goal with |- _ /\ _ => split end; first [assumption | lia | rewrite ERS, VH; reflexivity | idtac]. }
    idtac "MARK arm B junction facts".
    assert (PFU : forall a, usp <= a < 140737488355328 -> PF a).
    { intros a Ha. unfold PF. split; [left; unfold USTACK_TOP; clear - Ha; lia| cbn [outside]; clear - Ha CKR LOW LOR; lia]. }
    assert (UCXj : chain_ok mj usp (bv_unsigned s0) [RA_TOP]).
    { rewrite <- RAS. apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX). eapply agree_sub; [exact AGF|]. cbv beta. intros zx Hzx. apply PFU. unfold USTACK_TOP in Hzx. clear - Hzx. lia. }
    assert (FP1R : 0 <= bv_unsigned s0 < 2^64) by (pose proof (bv_unsigned_in_range 64 s0) as X; unfold bv_modulus in X; change (2 ^ Z.of_N 64) with (2^64) in X; exact X).
    eapply cps_seq.
    { eapply (d2_mid RT AF GP RC CML SCM CMF) with (lo := lo) (sa := usp + -256) (usp := usp) (fr := fr) (pixd := pixd) (dat := dat) (rd := rs) (datas := dtt)
         (rs := rst) (wpls := p_wpl vt) (wpld := p_wpl v1) (w := p_w v) (h := p_h v) (fp1 := bv_unsigned s0) (vd := vd) (frs0 := rt_frames RT Σ).
      all: lazymatch goal with
       | |- fdfs_only _ => exact FDO
       | |- mat_stable _ => exact MST
       | |- d2m_geom _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact GEOM
       | |- pix_obj _ _ _ _ _ => exact PODj
       | |- In _ (rt_live _ _) => exact DTIN
       | |- rt_frames _ _ = _ => exact FRSp
       | |- chain_ok _ _ _ _ => exact UCXj
       | |- ART _ _ _ => exact ARTj
       | |- wr_at _ _ _ _ => exact WLO
       | |- rw_cells _ _ ?A (CB 8 _ :: _) => lazymatch type of FRBLK with rw_cells _ _ ?B _ => replace A with B by (clear; lia) end; exact FRBLK
       | |- rw_cells _ ?mm ?A ?cs => first [ assumption | match goal with H : rw_cells _ mm ?B cs |- _ => replace A with B by (clear; lia); exact H end | idtac "LEFT-cells" A ]
       | |- Z.of_nat (length (rt_live _ _)) + _ <= _ => rewrite LVPB; cbn [length]; clear - LVB; unfold LIVE_MAX in *; lia
       | |- Z.of_nat (length (rt_frames _ _)) + _ <= _ => rewrite FRSp; cbn [length]; clear - FRB; unfold FRAMES_MAX in *; lia
       | |- _ <= rt_credit _ _ => clear - CRp CRB; unfold RASTER_COST in *; lia
       | |- forall p n, In (p, n) _ -> 0 < n => intros p n Hp; rewrite LVPB in Hp; cbn [In] in Hp; destruct Hp as [E|[E|[E|[E|Hp]]]]; [injection E as <- <-; exact DTN| injection E as <- <-; clear; lia| injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| exact (LVP p n Hp)]
       | |- 0 <= bv_unsigned _ < _ => exact FP1R
       | |- _ => first [assumption | reflexivity | lazymatch goal with |- ?g => idtac "MID SIDE LEFT:" g end]
       end. }
    idtac "MARK arm B mid applied".
    clear PODj GEOM WLO UCXj FP1R C48 FRBLK UREC FW FH FPD.
    hide FR. hide FRM. hide FSH. hide PXS. hide PXT. clear PXD.
    after_call RT AF.
    idtac "MARK arm B after mid".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σm; rename A into ARTM; rename mm into mmid end.
    lazymatch goal with H : rt_live RT Σm = (?ca, 16) :: (?cm, 24) :: rt_live RT Σp |- _ => rename H into LVMN; rename ca into carr; rename cm into cmap end.
    lazymatch goal with H : cmap_obj _ mmid cmap _ |- _ => rename H into CMO end.
    lazymatch goal with H : rw_cells asegs mmid pixd (pix_cells _) |- _ => rename H into PXD end.
    lazymatch goal with H : rw_cells asegs mmid (usp + -256 + 24) _ |- _ => rename H into S24 end.
    lazymatch goal with H : agree_on (d2m_keep _ _ _ _ _ _) mj mmid |- _ => rename H into AGM end.
    lazymatch goal with H : forall e, In e (rt_live RT Σp) -> fst e <> cmap /\ fst e <> carr |- _ => rename H into FZ end.
    lazymatch goal with H : forall a, d2m_keep _ _ _ _ _ _ a -> _ /\ _ |- _ => rename H into NCX end.
    assert (LVM : rt_live RT Σm = (carr, 16) :: (cmap, 24) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVMN, LVPB; reflexivity).
    assert (FRSm : rt_frames RT Σm = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σm = _ |- _ => rewrite E end; exact FRSp).
    assert (SP0m : rt_sp0 RT Σm = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σm = _ |- _ => rewrite E end; first [reflexivity | exact SP0p]).
    assert (CRm : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σm) by (lazymatch goal with E : rt_credit RT Σp - 6 <= rt_credit RT Σm |- _ => clear - E CRp; lia end).
    assert (LSUBm : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σm)) by (intros e He; rewrite LVM; do 6 right; exact He).
    pose proof CMO as ((cpad & CMC) & (KMIN & KM0 & KM16 & _) & (KAIN & KA0 & KA16 & _) & KOK & KANE).
    unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC, KAIN, KA0, KA16, KANE.
    destruct (FZ _ PDINp) as [NCMP NCAP]. destruct (FZ _ DDINp) as [NCMD NCAD]. destruct (FZ _ PINp) as [NCMX NCAX]. destruct (FZ _ DINp) as [NCMS NCAS].
    destruct (FZ _ PTIN) as [NCMT NCAT]. destruct (FZ _ DTIN) as [NCMU NCAU].
    cbn [fst] in NCMP, NCAP, NCMD, NCAD, NCMX, NCAX, NCMS, NCAS, NCMT, NCAT, NCMU, NCAU.
    assert (DDXT : dat + rs <= pixt \/ pixt + 64 <= dat)
      by (apply (live_apart2 RT AF Σm mmid dat rs pixt 64 ARTM); [rewrite LVM; do 4 right; left; reflexivity| rewrite LVM; do 3 right; left; reflexivity| intros E; injection E; intros _ E1; exact (NDT E1)]).
    idtac "MARK arm B mid names".
    (* [comment removed for export] *)
    unfold hid in FR.
    (* [comment removed for export] *)
    pose proof FR as P0. split_at P0 1%nat T.
    tryif constr_eq (0)%Z 0%Z then (split_at T 1%nat T40; split_last_CB T [8%nat; 24%nat]; split_at T 1%nat Tw; clear Tw; rename T into P8)
                                 else (split_at T 2%nat T40; clear T).
    split_at T40 2%nat Tm. split_at Tm 8%nat P144. clear Tm FR.
    unfold d2m_keep, d2m_W in AGM.
    carry AGM P0 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR1 CKR2 LOW LOR; repeat split; try exact I; lia).
    try (carry AGM P8 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR1 CKR2 LOW LOR; repeat split; try exact I; lia)).
    carry AGM T40 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR1 CKR2 LOW LOR; repeat split; try exact I; lia).
    carry AGM P144 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR1 CKR2 LOW LOR; repeat split; try exact I; lia).
    carry AGM FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [rewrite FRSp; left; reflexivity| change (fs_size 2%nat) with 256; clear - Hx; lia])
                  ltac:(fun Hx => unpark FCD1; unpark FCD2; clear - Hx FCD1 FCD2 FRHI LOW LOR; repeat split; try exact I; lia).
    carry AGM FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [rewrite FRSp; left; reflexivity| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia])
                  ltac:(fun Hx => unpark FCS1; unpark FCS2; unfold shad, SHB in *; clear - Hx FCS1 FCS2 FR64 FRHI SP0R1 SP0W LOW LOR; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    carry AGM PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [exact PINp| exact Hx])
                  ltac:(fun Hx => unpark DSD; unpark DSP; clear - Hx DSD DSP CKR LOW LOR; repeat split; try exact I; lia).
    carry AGM PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [exact PTIN| exact Hx])
                  ltac:(fun Hx => unpark DPXT; repeat match goal with H : pixt + 64 <= rt_sp0 RT Σ - _ |- _ => revert H end; clear - Hx DPXT DDXT LOW LOR; intros; repeat split; try exact I; lia).
    idtac "MARK arm B carried m".
    fold_ag ltac:(fun Hx => pose proof (PFS _ Hx) as P1; pose proof (NCD _ Hx) as N1; pose proof (NCP _ Hx) as N2; destruct Hx as [Hx1 Hx2]; split;
                   [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [exact LSUBp| intros e He; rewrite FRSp; right; exact He| clear; lia]
                   | cbn [outside]; clear - P1 N1 N2 LOR; repeat split; try exact I; lia]).
    idtac "MARK arm B folded m".
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (SUBT' : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> pixt)
      by (intros e He; apply (fresh_chunk_ne RT AF Σm mmid [(carr, 16); (cmap, 24); (dtt, rst)] pixt 64 ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) e ARTM);
          [rewrite LVM; reflexivity| cbn [app In]; do 3 right; exact He| clear; lia| destruct He as [<-|[<-|He]]; [exact DDN| cbn; clear; lia| destruct e as [q k]; exact (LVP q k He)]]).
    assert (SUBDT' : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> dtt)
      by (intros e He; apply (fresh_chunk_ne RT AF Σm mmid [(carr, 16); (cmap, 24)] dtt rst ((pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) e ARTM);
          [rewrite LVM; reflexivity| cbn [app In]; do 3 right; exact He| exact DTN| destruct He as [<-|[<-|He]]; [exact DDN| cbn; clear; lia| destruct e as [q k]; exact (LVP q k He)]]).
    sigma_gc RT Σ Σm.
    assert (CMINm : In (cmap, 24) (rt_live RT Σm)) by (rewrite LVM; right; left; reflexivity).
    assert (CAINm : In (carr, 16) (rt_live RT Σm)) by (rewrite LVM; left; reflexivity).
    assert (PDINm : In (pixd, 64) (rt_live RT Σm)) by (rewrite LVM; do 5 right; left; reflexivity).
    assert (DDINm : In (dat, rs) (rt_live RT Σm)) by (rewrite LVM; do 4 right; left; reflexivity).
    assert (PTINm : In (pixt, 64) (rt_live RT Σm)) by (rewrite LVM; do 3 right; left; reflexivity).
    assert (DTINm : In (dtt, rst) (rt_live RT Σm)) by (rewrite LVM; do 2 right; left; reflexivity).
    assert (PINm : In (pix, 64) (rt_live RT Σm)) by (apply LSUBm; exact PIN).
    assert (DINm : In (p_data v, 4 * (p_wpl v * p_h v)) (rt_live RT Σm)) by (apply LSUBm; exact DIN).
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    chunk_facts RT AF GP cmap 24. chunk_facts RT AF GP carr 16.
    fframe_chunk RT AF fr 2%nat 256 cmap 24. fframe_chunk RT AF fr 2%nat 256 carr 16.
    pose proof (live_apart2 RT AF Σm _ cmap 24 pix 64 ARTM CMINm PINm ltac:(intros E; injection E as E1 _; exact (NCMX (eq_sym E1)))) as ACMX.
    pose proof (live_apart2 RT AF Σm _ cmap 24 pixd 64 ARTM CMINm PDINm ltac:(intros E; injection E as E1 _; exact (NCMP (eq_sym E1)))) as ACMP.
    park_disj. park_ne.
    idtac "MARK arm B cm facts".
    (* [comment removed for export] *)
    lazymatch goal with WW1 : wr_at asegs ?mc (usp + -256 + 16) 24, WW2 : wr_at asegs ?mc (usp + -256 + 56) 88 |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      destruct (wr_at_rw_CB mc (usp + -256 + 16) 8 (wr_at_sub mc (usp + -256 + 16) 24 (usp + -256 + 16) 8 WW1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as [j16 P16];
      destruct (wr_at_rw_CB mc (usp + -256 + 32) 8 (wr_at_sub mc (usp + -256 + 16) 24 (usp + -256 + 32) 8 WW1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as [j32 P32];
      destruct (wr_at_rw_CB mc (usp + -256 + 56) 88 WW2 ltac:(clear; lia)) as [j56 P56]; clear WW1 WW2 end.
    change (Z.to_nat 8) with 8%nat in P16, P32. change (Z.to_nat 88) with 88%nat in P56.
    try (join_cells P0 P8). join_cells P0 P16. join_cells P0 S24. join_cells P0 P32. join_cells P0 T40. join_cells P0 P56. join_cells P0 P144.
    rename P0 into FR.
    idtac "MARK arm B FR rebuilt".
    (* [comment removed for export] *)
    try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
    walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDestroy].
    idtac "MARK arm B at pixDestroy".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    split_at FRM 10%nat PPC. split_at PPC 1%nat FRMb.
    pose proof FSH as SH10. split_at SH10 10%nat SH10b. split_at SH10b 1%nat SH10c. clear SH10 SH10c.
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    rewrite <- (Z_to_bv_bv_unsigned s0) in FRrec2. rewrite <- (Z_to_bv_bv_unsigned ra), RAF in FRrec2.
    unfold hid in HOKT, PXT.
    lazymatch goal with PT : rw_cells asegs ?mc pixt _ |- cps _ (ASTA RT Σm _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (POT4 : pix_obj (rt_live RT Σm) mc pixt vt (mkCmapv 0 0 0 0))
        by (split; [unfold pix_cells; rewrite WT, HT, DT, CMT; fold dtt; exact PT|]; split; [split; [exact PTINm| split; [exact PT0| split; [exact PT16| clear; lia]]]|];
            split; [exact HOKT|]; split; [right; split; [split; [exact DTINm| split; [exact DT0| split; [exact DT16| exact DTN]]]| unpark DTNE; exact DTNE]| left; exact CMT]);
      assert (OPP : optrL RT (live_destroy pixt vt (mkCmapv 0 0 0 0) (rt_live RT Σm)) Σm mc (fr + 80) 8)
        by (unfold optrL, accok; split;
            [ right; exists fr, 2%nat; rewrite FRSm; change (fs_size 2) with 256;
              split; [left; reflexivity|]; split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FR0; lia|];
              split; [clear - FRHI SP0R1; lia|];
              replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
              destruct SH10b as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B
            | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; unfold SEGTOP_A; split; [unpark FRSH; clear - FRSH; lia| clear - FRSEG; lia] ]);
      assert (UCC : chain_ok mc (usp + -256) usp [RA_FUZZ_OP1; RA_TOP])
        by (apply (chain_ok_push mc (usp + -256) usp RA_FUZZ_OP1 (bv_unsigned s0) [RA_TOP]);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | unfold RA_FUZZ_OP1; clear; lia
              | let X := fresh "X" in pose proof (bv_unsigned_in_range 64 s0) as X; unfold bv_modulus in X; change (2 ^ Z.of_N 64) with (2^64) in X; exact X | exact FRrec2
              | rewrite <- RAS; apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
    hide HOKT. clear FRrec2.
    idtac "MARK arm B destroy args".
    assert (CR1 : 1 <= rt_credit RT Σm) by (clear - CRm CRB; unfold RASTER_COST in *; lia).
    eapply cps_seq.
    { eapply DES with (lo := lo) (pp := fr + 80) (pix := pixt) (v := vt) (cv := mkCmapv 0 0 0 0) (ras := [RA_FUZZ_OP1; RA_TOP]).
      - exact FDO.
      - exact MST.
      - reflexivity.
      - reflexivity.
      - exact OPP.
      - exact PPC.
      - exact POT4.
      - unfold uctx. rewrite !unsigned_lit by (clear - USP0 USP1 LOR STa; lia). exact UCC.
      - unfold DESTROY_FREE_RAS, RA_FUZZ_OP1, RA_TOP. rewrite unsigned_lit by (clear; lia).
        repeat (apply Forall_cons; [apply ct_mem_In; vm_compute; reflexivity |]). apply Forall_nil.
      - lenv_tac.
      - unfold lres; rewrite FRSm, LVM; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [clear - FRB; lia| clear - LVB; lia| exact CR1|
          intros p n Hp; destruct Hp as [E|[E|[E|[E|[E|[E|Hp]]]]]];
          [ injection E; intros <- <-; clear; lia | injection E; intros <- <-; clear; lia | injection E; intros <- <-; exact DTN | injection E; intros <- <-; clear; lia
          | injection E; intros <- <-; exact DDN | injection E; intros <- <-; clear; lia | exact (LVP p n Hp)]]. }
    idtac "MARK arm B DES applied".
    clear POT4 OPP UCC CR1 SH10b.
    hide FRM. hide FRMb. hide FSH. hide PXD. hide PXS. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σz; rename A into ARTZ end.
    assert (LVZ : rt_live RT Σz = (carr, 16) :: (cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ).
    { repeat match goal with E : rt_live RT Σz = _ |- _ => rewrite E end. rewrite LVM.
      unpark DTNE.
      apply (live_destroy_d2t ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) pixt dtt rst cmap carr 16 vt (mkCmapv 0 0 0 0));
        [ reflexivity | exact CMT | clear - DT0; lia | exact DTNE | exact (not_eq_sym NCAU) | exact (not_eq_sym NCMU) | exact (not_eq_sym NCAT) | exact (not_eq_sym NCMT)
        | exact SUBT' | exact SUBDT' ]. }
    assert (FRSz : rt_frames RT Σz = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σz = _ |- _ => rewrite E end; exact FRSm).
    assert (SP0z : rt_sp0 RT Σz = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; first [reflexivity | exact SP0m]).
    assert (CRz : rt_credit RT Σ - (2 * RASTER_COST + 32) <= rt_credit RT Σz) by (lazymatch goal with E : rt_credit RT Σm - 1 <= rt_credit RT Σz |- _ => clear - E CRm; lia end).
    assert (LSUBz : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σz)) by (intros e He; rewrite LVZ; do 4 right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => clear - Hx; lia);
      carry AGx FRMb ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => clear - Hx; lia);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia])
                    ltac:(fun Hx => unpark FRSH; unfold shad, SHB in *; clear - Hx FR64 FRSH; first [lia | Z.div_mod_to_equations; lia]);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [rewrite LVZ; do 3 right; left; reflexivity| exact Hx]) ltac:(fun Hx => fcell_side fr pixd Hx);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [rewrite LVZ; do 4 right; exact PIN| exact Hx]) ltac:(fun Hx => fcell_side fr pix Hx);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [rewrite LVZ; right; left; reflexivity| exact Hx]) ltac:(fun Hx => fcell_side fr cmap Hx) end.
    idtac "MARK arm B carried z".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; destruct (NFA _ (conj Hx1 Hx2)) as [N1 N2]; clear - N1; repeat split; try exact I; lia).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK arm B after destroy".
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT Σz ?mm |- _ => rename mm into mz end.
    assert (FZP : forall e, In e (rt_live RT Σ) -> fst e <> pixd) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(carr, 16); (cmap, 24); (dat, rs)] pixd 64 (rt_live RT Σ) e ARTZ); [rewrite LVZ; reflexivity| cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [q k]; exact (LVP q k He)]).
    assert (FZD : forall e, In e (rt_live RT Σ) -> fst e <> dat) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(carr, 16); (cmap, 24)] dat rs ((pixd, 64) :: rt_live RT Σ) e ARTZ); [rewrite LVZ; reflexivity| cbn [app In]; do 3 right; exact He| exact DDN| destruct e as [q k]; exact (LVP q k He)]).
    assert (FZC : forall e, In e (rt_live RT Σ) -> fst e <> cmap) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(carr, 16)] cmap 24 ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) e ARTZ); [rewrite LVZ; reflexivity| cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [q k]; exact (LVP q k He)]).
    assert (FZA : forall e, In e (rt_live RT Σ) -> fst e <> carr) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [] carr 16 ((cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) e ARTZ); [rewrite LVZ; reflexivity| cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [q k]; exact (LVP q k He)]).
    assert (PDINz : In (pixd, 64) (rt_live RT Σz)) by (rewrite LVZ; do 3 right; left; reflexivity).
    assert (DDINz : In (dat, rs) (rt_live RT Σz)) by (rewrite LVZ; do 2 right; left; reflexivity).
    assert (CMINz : In (cmap, 24) (rt_live RT Σz)) by (rewrite LVZ; right; left; reflexivity).
    assert (CAINz : In (carr, 16) (rt_live RT Σz)) by (rewrite LVZ; left; reflexivity).
    assert (PINz : In (pix, 64) (rt_live RT Σz)) by (apply LSUBz; exact PIN).
    assert (DINz : In (p_data v, 4 * (p_wpl v * p_h v)) (rt_live RT Σz)) by (apply LSUBz; exact DIN).
    sigma_gc RT Σ Σz.
    repeat match goal with H : In (?b, _) (rt_live RT Σ) |- _ => lazymatch b with pix => fail | p_data v => fail | _ => clear H end end.
    idtac "MARK arm B diet".
    hide PXS. hide PXD. hide CMC.
    try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0xa0020].
    idtac "MARK arm B at flag load".
    idtac "MARK arm B at pokes".
    try unfold hid in FRM. try unfold hid in FSH. split_at FRM 1%nat FRMr.
    Time (eapply evt_cut;
    [ eapply EVQ_exit;
      [ eapply d2bpp_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
      | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
    | ]).
    clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold d2bpp_exit_W, SHB in MUx. unfold d2bpp_sh_f5 in FSH.
    idtac "MARK arm B pokes applied".
    Time loop_art RT AF Σz mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    Time (lazymatch type of MUx with munch _ ?ma ?mb =>
      loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *;
          first [pose proof FRSEG as XFRSEG | pose proof I as XFRSEG]; first [pose proof SP0W as XSP0W | pose proof I as XSP0W]; first [pose proof FRSH as XFRSH | pose proof I as XFRSH];
          clear - Hx FRHI LOW LOR FR64 FR0 SP0R1 SP0R0 XFRSEG XSP0W XFRSH;
          unfold parked, hid in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end).
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => chunk_side fr pix FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx);
      carry_mu MUx PXD ltac:(fun Hx => chunk_side fr pixd FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx);
      carry_mu MUx CMC ltac:(fun Hx => chunk_side fr cmap FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx) end.
    hide PXS. hide PXD. hide CMC.
    join_cells FRM FRMr.
    idtac "MARK arm B carried x".
    frame_release_g RT AF GP MST Σ fr 2%nat 256 PF AGF PFS usp lo 0xa00d4
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => agf_side PFS NFA LOR Hx) ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
    idtac "MARK arm B frame released".
    lazymatch goal with MUx : munch [(?fl, ?fl + 1)] _ ?mb |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => repeat match goal with Hf : fl < pix \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx PXD ltac:(fun Hx => repeat match goal with Hf : fl < pixd \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx CMC ltac:(fun Hx => repeat match goal with Hf : fl < cmap \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia) end.
    hide PXS. hide PXD. hide CMC.
    clear_acc. refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    try forget_junk_in (usp + -256). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
    walk_to AF MST [(usp - 256, usp)] (@nil Z).
    lazymatch goal with MUx : munch _ _ ?mb |- evt _ _ (MS _ _ _ _ _ ?mb _) =>
      carry_mu MUx PXS ltac:(fun Hx => chunk_side fr pix FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx);
      carry_mu MUx PXD ltac:(fun Hx => chunk_side fr pixd FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx);
      carry_mu MUx CMC ltac:(fun Hx => chunk_side fr cmap FRSH FRHI SP0R0 SP0R1 LOW LOR FR64 FR0 Hx) end.
    cps_stop.
    idtac "MARK arm B epilogue walked".
    (* [comment removed for export] *)
    apply cps_finish; intros c Hc; subst QF; unfold d2bpp_post; cbv beta.
    set (vf := mkPixv (p_w v) (p_h v) 2 (p_spp v1) (p_wpl v1) (p_xres v) (p_yres v) (p_inf v) (p_spec v1) cmap dat).
    unfold hid in HOKD, PXS, PXD, CMC.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, pixd, vf, (mkCmapv carr 2 4 4) end.
    split.
    2: {
    split; [intros Z0; exfalso; clear - Z0 PD0; lia|].
    split.
    { intros _. rewrite LV2, LVZ.
      unpark VDATA1; unpark DDNE; unpark NCMP; unpark NCAP; unpark NCMD; unpark NCAD; unpark KANE.
      apply (live_destroy_d2 (rt_live RT Σ) pixd dat rs cmap carr 16 vf (mkCmapv carr 2 4 4));
        [reflexivity| reflexivity| reflexivity| exact VDATA1| clear - KM0; lia| clear - KA0; lia
        | exact DDNE| exact NCAD| exact NCMD| intro E; apply NCAP; symmetry; exact E| intro E; apply NCMP; symmetry; exact E| intro E; apply KANE; symmetry; exact E
        | exact FZP| exact FZD| exact FZC| exact FZA]. }
    split.
    { intros p n Hp. rewrite LV2, LVZ in Hp. cbn [In] in Hp.
      destruct Hp as [E|[E|[E|[E|Hp]]]]; [injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| exact (LVP p n Hp)]. }
    split; [rewrite LV2, LVZ; cbn [length]; clear; lia|].
    split; [rewrite FRS2; first [reflexivity | exact FRSz]|]. split; [rewrite SP2; first [exact SP0z | reflexivity]|].
    unfold D2_COST, OP_COST, is_d8. cbn [Z.eqb Pos.eqb]. rewrite CR2. clear - CRz. unfold RASTER_COST in *. lia.
    }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    split; [unfold lpost_f, rt_after_f; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); split; [split; [assumption| split; assumption]| split; assumption]|].
    split; [unfold keepsL, rt_pres_fp; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
    split.
    { rewrite LV2, LVZ. lazymatch goal with PS : rw_cells asegs ?mc pix _ |- pix_obj _ ?mc _ _ _ =>
        exact (PSRC ((carr, 16) :: (cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) 1 mc ltac:(intros e He; do 4 right; exact He) AGF PS) end. }
    right. split; [| cbn [p_data]; unpark VDATA1; exact VDATA1].
    rewrite LV2, LVZ.
    split; [unfold pix_cells, vf; unfold vd in PXD; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD |- *; exact PXD|].
    split; [split; [do 3 right; left; reflexivity| split; [exact PD0| split; [exact PD16| clear; lia]]]|].
    split; [unfold pix_hdr_ok in HOKD |- *; unfold vf; cbn [p_w p_h p_d p_wpl]; rewrite VW, VH, VD in HOKD; exact HOKD|].
    split; [right; unfold vf, rsize; cbn [p_data p_wpl p_h]; split; [split; [do 2 right; left; rewrite <- VH; reflexivity| split; [exact DD0| split; [exact DD16| rewrite <- VH; exact DDN]]]| unpark DDNE; exact DDNE]|].
    right. unfold vf; cbn [p_cmap p_data c_arr].
    split.
    { split; [exists cpad; unfold cmap_cells; cbn [c_arr c_depth c_nalloc c_n]; exact CMC|].
      split; [split; [right; left; reflexivity| split; [exact KM0| split; [exact KM16| clear; lia]]]|].
      split; [cbn [c_arr c_nalloc]; split; [left; reflexivity| split; [exact KA0| split; [exact KA16| clear; lia]]]|].
      split; [exact KOK| cbn [c_arr]; unpark KANE; exact KANE]. }
    unpark NCMP; unpark NCAP; unpark NCMD; unpark NCAD.
    repeat split; intro E; [apply NCMP | apply NCAP | apply NCMD | apply NCAD]; symmetry; exact E.
Qed.

End D2BPPC.
