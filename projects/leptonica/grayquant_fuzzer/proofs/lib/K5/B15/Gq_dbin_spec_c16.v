(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
  Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Lept_chain Lept_gmax_defs
  Gm_iface Gq_obj Gq_iface Gq_dbin_defs Gq_dither_low.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Lept_fuzzkit Lept_deserkit Gm_kit Gm_livekit Gm_livekit2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Gq_dbin_exit.
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
Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ ?m ?B ?cs2 =>
    let J := fresh "J" in
    assert (J : rw_cells asegs m A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app m A cs1 cs2)); split;
          [ exact H1
          | cbn [cells_size csize Nat.add]; lazymatch goal with |- rw_cells _ _ ?X _ => replace X with B by (clear; lia) end; exact H2 ]);
    clear H1 H2; cbn [app] in J; rename J into H1 end end.
Local Ltac park_ne := repeat match goal with H : (?a <> ?b) |- _ => lazymatch type of a with Z => change (a <> b) with (parked (a <> b)) in H end end.

Section DBINC.
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

(* [comment removed for export] *)
Local Ltac forget_junk H :=
  repeat match type of H with context [CB _ ?bs] =>
    lazymatch bs with
    | firstn _ _ => let j := fresh "jq" in set (j := bs) in *; clearbody j
    | skipn _ _ => let j := fresh "jq" in set (j := bs) in *; clearbody j
    end end.

Local Ltac eqv :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity.

Lemma dbin_spec_c16 : dbin_spec_case RT 16.
Proof using AF GP RC RERR PCS PCR PCI PRC PDR DES.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    FDO MST -> -> -> -> POBJ VDATA CNZ D8 UC RAF RAS ENV RES AL.
  unfold lpost_f, lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  unfold DBIN_COST, OP_COST, is_d8, MSG_COST in *. cbn [Z.eqb Pos.eqb] in CRB.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixDitherToBinarySpec, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
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
  carve_frame 208%nat ST.
  walk_to AF MST [(usp - 208, usp)] [e_stack_malloc 2%nat].
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
  walk_to AF MST [(usp - 208, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9dbc4].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx => agf_side PFS NFA LOR Hx) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH. local_acc FSH fr 8%nat 64 FR64 FR1 ACCD.
  park_disj.
  idtac "MARK header done".
  try forget_junk FR; try forget_junk FRM; try forget_junk FSH.
  walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCreate; 0x9dc6c; 0x9dc34; 0x9dcac; e_stack_malloc 2%nat].
  idtac "MARK after dims".
  try (rewrite D8; brF).
  awalk [e_pixCreate; 0x9dcb0; 0x9dbfc].
  idtac "MARK at pixCreate".
  rewrite ?(sx32_small (p_w v)) by (clear - HW0 HW2; lia). rewrite ?(sx32_small (p_h v)) by (clear - HH0 HH2; lia).
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => agf_side PFS NFA LOR Hx).
  idtac "MARK at_call pixCreate".
  assert (WR : 0 < p_w v <= 20000) by (clear - HW0 HW2; lia). assert (HR : 0 < p_h v <= 20000) by (clear - HH0 HH2; lia).
  assert (HAO : hdr_args_ok (p_w v) (p_h v) 1) by (unfold hdr_args_ok; split; [cbn [In]; tauto|]; split; [exact WR|]; split; [exact HR|]; clear - WR HR; split; [| assert ((p_w v * 1 + 31) / 32 <= 626) by (Z.div_mod_to_equations; lia); nia]; assert (1 <= (p_w v * 1 + 31) / 32) by (Z.div_mod_to_equations; lia); nia).
  assert (CRD : 2 * RASTER_COST + 64 - 1 <= rt_credit RT Σ) by (clear - CRB; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; lia).
  eapply cps_seq.
  {
  eapply PCS with (lo := lo) (w := p_w v) (h := p_h v) (d := 1).
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
  try forget_junk FR; try forget_junk FRM; try forget_junk FSH.
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
  assert (EWD : p_wpl v1 = (p_w v + 31) / 32) by (destruct HOKD as (_ & _ & _ & Q4 & _); rewrite VW, VD in Q4; rewrite Q4; f_equal; lia).
  assert (ERS : rs = 4 * (p_wpl v1 * p_h v)) by (unfold rs, rsize; rewrite VH; reflexivity).
  assert (RSD : 0 < 4 * (p_wpl v1 * p_h v) <= 67108864) by (destruct HOKD as (_ & _ & _ & _ & Q5); rewrite VH in Q5; exact Q5).
  hide POD. hide SUBP. hide SUBD. hide HOKD.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK before walk to PCR".
  walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCopyResolution; 0x9dde4].
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
  walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCopyInputFormat; 0x9dde4].
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
  walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixRemoveColormap; 0x9dde4].
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
    assert (UCC : chain_ok mc (usp + -208) usp (bv_unsigned ra :: ras))
      by (apply (chain_ok_push _ (usp + -208) usp (bv_unsigned ra) (bv_unsigned s0) ras);
            [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP2; clear; lia
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
  - intros _. rewrite RAF, RAS. unfold REMOVE_RAS, RA_FUZZ_OP2, RA_TOP. rewrite unsigned_lit by (clear; lia).
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
  try forget_junk FR; try forget_junk FRM; try forget_junk FSH.
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
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9de1c].
    idtac "MARK arm A at calloc 1".
    assert (WPLO : 0 < p_wpl v) by (rewrite EWS; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    assert (WPHI : p_wpl v <= 5001) by (rewrite EWS; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    rewrite !(sx32_small (p_wpl v)) by (clear - WPLO WPHI; lia).
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 1".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc1 : In (0x9dd7c :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT Σp _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -208) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -208) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP2; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := p_wpl v) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRc1]
           | |- _ => first [ unfold CALLOC_MAX; clear - WPLO WPHI; lia
                           | rewrite LVPA; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                           | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
           end. }
    idtac "MARK calloc 1 applied".
    clear UCC.
    after_call RT AF.
    fold_pres usp.
    idtac "MARK after calloc 1".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σb1; rename A into ARTB1 end.
    lazymatch goal with H : rt_live RT Σb1 = (?p, _) :: _ |- _ => rename H into LVB1N; rename p into bufs1 end.
    lazymatch goal with H : rw_cells asegs _ bufs1 [CB _ _] |- _ => rename H into B1Z end.
    assert (LVB1 : rt_live RT Σb1 = (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVB1N, LVPA; reflexivity).
    assert (FRSb1 : rt_frames RT Σb1 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σb1 = _ |- _ => rewrite E end; exact FRSp).
    assert (SP0b1 : rt_sp0 RT Σb1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRb1 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σb1) by (repeat match goal with E : rt_credit RT Σb1 = _ |- _ => rewrite E end; exact CRp).
    lazymatch goal with H : 0 < bufs1 |- _ => rename H into B10 end.
    lazymatch goal with H : bufs1 mod 16 = 0 |- _ => rename H into B116 end.
    chunk_facts RT AF GP bufs1 (p_wpl v * 4). fframe_chunk RT AF fr 2%nat 256 bufs1 (p_wpl v * 4).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9de1c].
    idtac "MARK arm A at calloc 2".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 2".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc2 : In (0x9dd8c :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -208) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -208) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP2; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := p_wpl v) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRc2]
           | |- _ => first [ unfold CALLOC_MAX; clear - WPLO WPHI; lia
                           | rewrite LVB1; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                           | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
           end. }
    idtac "MARK calloc 2 applied".
    clear UCC.
    after_call RT AF.
    fold_pres usp.
    idtac "MARK after calloc 2".
    try forget_junk FR; try forget_junk FRM; try forget_junk FSH; try forget_junk FRMb.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σb2; rename A into ARTB2 end.
    lazymatch goal with H : rt_live RT Σb2 = (?p, _) :: _ |- _ => rename H into LVB2N; rename p into bufs2 end.
    lazymatch goal with H : rw_cells asegs _ bufs2 [CB _ _] |- _ => rename H into B2Z end.
    assert (LVB2 : rt_live RT Σb2 = (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVB2N, LVB1; reflexivity).
    assert (FRSb2 : rt_frames RT Σb2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σb2 = _ |- _ => rewrite E end; exact FRSb1).
    assert (SP0b2 : rt_sp0 RT Σb2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRb2 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σb2) by (repeat match goal with E : rt_credit RT Σb2 = _ |- _ => rewrite E end; exact CRb1).
    lazymatch goal with H : 0 < bufs2 |- _ => rename H into B20 end.
    lazymatch goal with H : bufs2 mod 16 = 0 |- _ => rename H into B216 end.
    chunk_facts RT AF GP bufs2 (p_wpl v * 4). fframe_chunk RT AF fr 2%nat 256 bufs2 (p_wpl v * 4).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_ditherToBinaryLow; 0x9de5c].
    idtac "MARK arm A at ditherToBinaryLow".
    rewrite ?(sx32_small (p_w v)) by (clear - HW0 HW2; lia). rewrite ?(sx32_small (p_h v)) by (clear - HH0 HH2; lia).
    assert (WPLD1 : 0 < p_wpl v1) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    assert (WPLD2 : p_wpl v1 <= 626) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    rewrite ?(sx32_small (p_wpl v1)) by (clear - WPLD1 WPLD2; lia).
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call DLOW".
    (* [comment removed for export] *)
    assert (NEB2 : forall e, In e ((bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> bufs2)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σb2 _ [] bufs2 (p_wpl v * 4) _ e ARTB2 LVB2); [cbn [app]; exact He| clear - WPLO; lia| exact Hn]).
    assert (NEB1 : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> bufs1)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σb1 _ [] bufs1 (p_wpl v * 4) _ e ARTB1 LVB1); [cbn [app]; exact He| clear - WPLO; lia| exact Hn]).
    assert (SUBB1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σb1) /\ fst e <> bufs1)
      by (intros e He; split; [rewrite LVB1; right; right; right; exact He| apply NEB1; [right; right; exact He| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBB2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σb2) /\ fst e <> bufs2)
      by (intros e He; split; [rewrite LVB2; right; right; right; right; exact He| apply NEB2; [right; right; right; exact He| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (NCB1 : forall a, PF a -> a < bufs1 \/ bufs1 + p_wpl v * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σb1 _ bufs1 (p_wpl v * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTB1 ltac:(rewrite LVB1; left; reflexivity) SUBB1);
          [ rewrite FRSb1; intros e He; right; exact He | rewrite SP0b1; ul | exact (proj1 Ha) ]).
    assert (NCB2 : forall a, PF a -> a < bufs2 \/ bufs2 + p_wpl v * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σb2 _ bufs2 (p_wpl v * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTB2 ltac:(rewrite LVB2; left; reflexivity) SUBB2);
          [ rewrite FRSb2; intros e He; right; exact He | rewrite SP0b2; ul | exact (proj1 Ha) ]).
    assert (ND4 : NoDup [dat; p_data v; bufs1; bufs2]).
    { pose proof (NEB2 (dat, rs) ltac:(right; left; reflexivity) DDN) as Q1. pose proof (NEB2 (bufs1, p_wpl v * 4) ltac:(left; reflexivity) ltac:(cbn [snd]; clear - WPLO; lia)) as Q2.
      pose proof (NEB2 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(right; right; right; exact DIN) DSZ) as Q3.
      pose proof (NEB1 (dat, rs) ltac:(left; reflexivity) DDN) as Q4. pose proof (NEB1 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(right; right; exact DIN) DSZ) as Q5.
      cbn [fst] in Q1, Q2, Q3, Q4, Q5. unfold parked in NSD. clear - Q1 Q2 Q3 Q4 Q5 NSD.
      nodup4. }
    idtac "MARK DLOW facts".
    eapply cps_seq.
    { pose proof (ditherToBinaryLow_ok RT AF GP RC) as DL; unfold ditherToBinaryLow_cps in DL;
      eapply DL with (lo := lo) (datad := dat) (w := p_w v) (h := p_h v) (wpld := p_wpl v1) (datas := p_data v) (wpls := p_wpl v) (bufs1 := bufs1) (bufs2 := bufs2); clear DL.
      all: lazymatch goal with
           | |- fdfs_only _ => exact FDO
           | |- mat_stable _ => exact MST
           | |- s32 _ _ => split; [| reflexivity]; first [clear - HW0 HW2; lia | clear - HH0 HH2; lia | clear - WPLD1 WPLD2; lia | clear - WPLO WPHI; lia]
           | |- @eq word _ _ => reflexivity
           | |- (0 < _ <= 20000) => first [clear - HW0 HW2; lia | clear - HH0 HH2; lia]
           | |- _ = (_ + 31) / 32 => first [rewrite EWD; reflexivity | rewrite EWS; reflexivity]
           | |- 4 * _ <= _ => clear - HRS1; lia
           | |- chunk _ _ (4 * (_ * _)) => first [ split; [rewrite LVB2, ERS; right; right; left; reflexivity| split; [exact DD0| split; [exact DD16| rewrite ERS in DDN; exact DDN]]]
                                                 | split; [rewrite LVB2; right; right; right; right; exact DIN| split; [exact D0| split; [exact D16| exact DSZ]]] ]
           | |- chunk _ _ (4 * _) => first [ split; [rewrite LVB2; right; left; f_equal; clear; lia| split; [exact B10| split; [exact B116| clear - WPLO; lia]]]
                                           | split; [rewrite LVB2; left; f_equal; clear; lia| split; [exact B20| split; [exact B216| clear - WPLO; lia]]] ]
           | |- NoDup _ => exact ND4
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => unfold lres; rewrite FRSb2, LVB2; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split;
                                   [clear - FRB; lia| clear - LVB; lia| clear - CRb2 CRB; unfold RASTER_COST in *; lia
                                   | intros p n Hp; destruct Hp as [E|[E|[E|[E|Hp]]]];
                                     [injection E; intros <- <-; clear - WPLO; lia | injection E; intros <- <-; clear - WPLO; lia | injection E; intros <- <-; exact DDN | injection E; intros <- <-; clear; lia | exact (LVP p n Hp)]]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK DLOW applied".
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT Σb2 ?mm |- _ =>
      pose proof (live_apart2 RT AF Σb2 mm pix 64 bufs1 (p_wpl v * 4) A ltac:(rewrite LVB2; right; right; right; right; exact PIN) ltac:(rewrite LVB2; right; left; reflexivity)
                    ltac:(intros E; injection E; intros _ E1; exact (NEB1 (pix, 64) ltac:(right; right; exact PIN) ltac:(cbn; clear; lia) E1))) as APS1;
      pose proof (live_apart2 RT AF Σb2 mm pix 64 bufs2 (p_wpl v * 4) A ltac:(rewrite LVB2; right; right; right; right; exact PIN) ltac:(rewrite LVB2; left; reflexivity)
                    ltac:(intros E; injection E; intros _ E1; exact (NEB2 (pix, 64) ltac:(right; right; right; exact PIN) ltac:(cbn; clear; lia) E1))) as APS2;
      pose proof (live_apart2 RT AF Σb2 mm pixd 64 bufs1 (p_wpl v * 4) A ltac:(rewrite LVB2; right; right; right; left; reflexivity) ltac:(rewrite LVB2; right; left; reflexivity)
                    ltac:(intros E; injection E; intros _ E1; exact (NEB1 (pixd, 64) ltac:(right; left; reflexivity) ltac:(cbn; clear; lia) E1))) as APD1;
      pose proof (live_apart2 RT AF Σb2 mm pixd 64 bufs2 (p_wpl v * 4) A ltac:(rewrite LVB2; right; right; right; left; reflexivity) ltac:(rewrite LVB2; left; reflexivity)
                    ltac:(intros E; injection E; intros _ E1; exact (NEB2 (pixd, 64) ltac:(right; right; left; reflexivity) ltac:(cbn; clear; lia) E1))) as APD2 end.
    hide FRM. hide FSH. hide PXD. hide PXS.
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => fr_side fr Hx);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => sh_side fr FR64 Hx);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx])
                    ltac:(fun Hx => unfold parked in DPD; clear - Hx DPD APD1 APD2 ERS; lia);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx])
                    ltac:(fun Hx => unfold parked in DSD; clear - Hx DSD APS1 APS2 ERS; lia) end.
    idtac "MARK carried".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; pose proof (NCD _ (conj Hx1 Hx2)) as Y1; pose proof (NCB1 _ (conj Hx1 Hx2)) as Y2; pose proof (NCB2 _ (conj Hx1 Hx2)) as Y3;
                              clear - Y1 Y2 Y3 ERS; repeat split; try exact I; lia).
    idtac "MARK after DLOW".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σd; rename A into ARTD end.
    assert (LVD : rt_live RT Σd = (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σd = _ |- _ => rewrite E end; exact LVB2).
    assert (FRSd : rt_frames RT Σd = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σd = _ |- _ => rewrite E end; exact FRSb2).
    assert (SP0d : rt_sp0 RT Σd = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRd : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σd) by (lazymatch goal with E : rt_credit RT Σb2 <= rt_credit RT Σd |- _ => clear - E CRb2; lia end).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9de5c].
    idtac "MARK arm A at free 1".
    assert (NPB1 : pixd <> bufs1) by (exact (NEB1 (pixd, 64) ltac:(right; left; reflexivity) ltac:(cbn; clear; lia))).
    assert (NPB2 : pixd <> bufs2) by (exact (NEB2 (pixd, 64) ltac:(right; right; left; reflexivity) ltac:(cbn; clear; lia))).
    assert (NSB1 : pix <> bufs1) by (exact (NEB1 (pix, 64) ltac:(right; right; exact PIN) ltac:(cbn; clear; lia))).
    assert (NSB2 : pix <> bufs2) by (exact (NEB2 (pix, 64) ltac:(right; right; right; exact PIN) ltac:(cbn; clear; lia))).
    assert (NB21 : bufs2 <> bufs1) by (intros E; apply (NEB2 (bufs1, p_wpl v * 4) ltac:(left; reflexivity) ltac:(cbn; clear - WPLO; lia)); symmetry; exact E).
    assert (NRB1 : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> bufs1)
      by (intros e He; apply (NEB1 e He); destruct He as [<-|[<-|He]]; [exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (NRB2 : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> bufs2)
      by (intros e He; apply (NEB2 e); [right; exact He|]; destruct He as [<-|[<-|He]]; [exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    park_ne.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call free 1".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf1 : In (0x9ddcc :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -208) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -208) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP2; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := bufs1) (n := p_wpl v * 4); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVD; right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf1]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK free 1 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf1; rename A into ARTF1 end.
    assert (LVF1 : rt_live RT Σf1 = (bufs2, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf1 = _ |- _ => rewrite E end; rewrite LVD; unfold parked in NB21; exact (live_remove_2nd bufs1 _ bufs2 _ _ NB21 NRB1)).
    assert (FRSf1 : rt_frames RT Σf1 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf1 = _ |- _ => rewrite E end; exact FRSd).
    assert (SP0f1 : rt_sp0 RT Σf1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf1 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σf1) by (repeat match goal with E : rt_credit RT Σf1 = _ |- _ => rewrite E end; exact CRd).
    assert (LSUBf1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf1)) by (intros e He; rewrite LVF1; right; right; right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [rewrite LVF1; right; right; left; reflexivity| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [rewrite LVF1; right; right; right; exact PIN| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK carried f1".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf1| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9de5c].
    idtac "MARK arm A at free 2".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf2 : In (0x9ddd4 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -208) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -208) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP2; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := bufs2) (n := p_wpl v * 4); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVF1; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf2]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK free 2 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf2; rename A into ARTF2 end.
    assert (LVF2 : rt_live RT Σf2 = (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf2 = _ |- _ => rewrite E end; rewrite LVF1; exact (live_remove_hd bufs2 _ _ NRB2)).
    assert (FRSf2 : rt_frames RT Σf2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf2 = _ |- _ => rewrite E end; exact FRSf1).
    assert (SP0f2 : rt_sp0 RT Σf2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf2 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σf2) by (repeat match goal with E : rt_credit RT Σf2 = _ |- _ => rewrite E end; exact CRf1).
    assert (LSUBf2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf2)) by (intros e He; rewrite LVF2; right; right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [rewrite LVF2; right; left; reflexivity| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [rewrite LVF2; right; right; exact PIN| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK carried f2".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf2| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDestroy; 0x9de5c].
    idtac "MARK arm A at pixDestroy".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call PDR".
    (* [comment removed for export] *)
    split_at FRM 10%nat PPC. split_at PPC 1%nat FRMb.
    pose proof FSH as SH10. split_at SH10 10%nat SH10b. split_at SH10b 1%nat SH10c. clear SH10 SH10c.
    lazymatch goal with PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σf2 _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (POS4 : pix_obj_rc (rt_live RT Σf2) mc pix v cv 2) by (exact (PSRC (rt_live RT Σf2) 2 mc LSUBf2 AGF PS));
      assert (OPP : optrL RT (rt_live RT Σf2) Σf2 mc (fr + 80) 8)
        by (unfold optrL, accok; split;
            [ right; exists fr, 2%nat; rewrite FRSf2; change (fs_size 2) with 256;
              split; [left; reflexivity|]; split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FR0; lia|];
              split; [clear - FRHI SP0R1; lia|];
              replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
              destruct SH10b as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B
            | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; unfold SEGTOP_A; split; [clear - FRSH; unfold parked in FRSH; lia| clear - FRSEG; unfold parked in FRSEG; lia] ]) end.
    idtac "MARK destroy args".
    assert (CR1 : 1 <= rt_credit RT Σf2) by (clear - CRf2 CRB; unfold RASTER_COST in *; lia).
    eapply cps_seq.
    {
    eapply PDR with (lo := lo) (pp := fr + 80) (pix := pix) (v := v) (cv := cv) (rc := 2).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - exact OPP.
    - exact PPC.
    - exact POS4.
    - clear; lia.
    - unfold parked in FCD; clear - FCD; lia.
    - lenv_tac.
    - unfold lres; rewrite FRSf2, LVF2; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [clear - FRB; lia| clear - LVB; lia| exact CR1|
        intros p n Hp; destruct Hp as [E|[E|Hp]]; [injection E; intros <- <-; exact DDN | injection E; intros <- <-; clear; lia | exact (LVP p n Hp)]].
    }
    idtac "MARK PDR applied".
    clear POS4 OPP CR1 SH10b.
    hide FRM. hide FRMb. hide FSH. hide PXD.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σz; rename A into ARTZ end.
    assert (LVZ : rt_live RT Σz = (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σz = _ |- _ => rewrite E end; exact LVF2).
    assert (FRSz : rt_frames RT Σz = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σz = _ |- _ => rewrite E end; exact FRSf2).
    assert (SP0z : rt_sp0 RT Σz = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRz : rt_credit RT Σ - (2 * RASTER_COST + 26) <= rt_credit RT Σz) by (lazymatch goal with E : rt_credit RT Σf2 - 1 <= rt_credit RT Σz |- _ => clear - E CRf2; lia end).
    assert (LSUBz : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σz)) by (intros e He; rewrite LVZ; right; right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => unfold parked in FCD; clear - Hx FCD; lia);
      carry AGx FRMb ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => unfold parked in FCD; clear - Hx FCD; lia);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia])
                    ltac:(fun Hx => unfold parked in FCS, FRSH; unfold shad, SHB in *; clear - Hx FCS FR64 FRSH CKH; first [lia | Z.div_mod_to_equations; lia]);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [rewrite LVZ; right; left; reflexivity| exact Hx]) ltac:(fun Hx => unfold parked in FCD1, DSP; clear - Hx FCD1 DSP; lia) end.
    idtac "MARK carried z".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; cbn [outside] in Hx2; destruct (NFA _ (conj Hx1 Hx2)) as [N1 N2]; clear - N1 Hx2; repeat split; try exact I; lia).
    lazymatch goal with H : rw_cells asegs _ pix (pix_cells_rc v (2 - 1)) |- _ => rename H into PXS end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    (* [comment removed for export] *)
    unfold hid in SUBP, SUBD.
    assert (SUBP' : forall e, In e (rt_live RT Σ) -> fst e <> pixd) by (intros e He; exact (proj2 (SUBP e He))).
    assert (SUBD' : forall e, In e (rt_live RT Σ) -> fst e <> dat) by (intros e He; exact (proj2 (SUBD e He))).
    clear SUBP SUBD.
    assert (PDINz : In (pixd, 64) (rt_live RT Σz)) by (rewrite LVZ; right; left; reflexivity).
    assert (DDINz : In (dat, rs) (rt_live RT Σz)) by (rewrite LVZ; left; reflexivity).
    assert (PINz : In (pix, 64) (rt_live RT Σz)) by (rewrite LVZ; right; right; exact PIN).
    assert (DINz : In (p_data v, 4 * (p_wpl v * p_h v)) (rt_live RT Σz)) by (rewrite LVZ; right; right; exact DIN).
    sigma_gc RT Σ Σz.
    repeat match goal with H : In (?b, _) (rt_live RT Σ) |- _ => lazymatch b with pix => fail | p_data v => fail | _ => clear H end end.
    idtac "MARK diet".
    try forget_junk FR; try forget_junk FRM; try forget_junk FSH; try forget_junk FRMb.
    hide PXS. hide PXD.
    (* [comment removed for export] *)
    repeat match goal with H : context [bufs1] |- _ => clear H end.
    repeat match goal with H : context [bufs2] |- _ => clear H end.
    try clear bufs1. try clear bufs2.
    repeat match goal with H : wmono _ _ ?b |- _ => lazymatch goal with |- context [b] => fail | _ => clear H end end.
    repeat match goal with H : munch _ _ ?b |- _ => lazymatch goal with |- context [b] => fail | _ => clear H end end.
    clear_acc.
    hide FCD. hide FCS. hide CKH. hide FCD1. hide FCS1. hide CKH1. hide DDNE. hide VDATA1. hide FRSH.
    repeat match goal with H : parked ?T |- _ => lazymatch T with context [fr] => hide H | _ => clear H end end.
    unfold hid in FRSH. unfold parked in FRSH.
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9debc].
    idtac "MARK at flag load".
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    idtac "MARK at pokes".
    try unfold hid in FRM. try unfold hid in FSH. split_at FRM 1%nat FRMr.
    Time (eapply evt_cut;
    [ eapply EVQ_exit;
      [ eapply dbin_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
      | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
    | ]).
    clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold dbin_exit_W, SHB in MUx. unfold dbin_sh_f5 in FSH.
    idtac "MARK pokes applied".
    Time loop_art RT AF Σz mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    Time (lazymatch type of MUx with munch _ ?ma ?mb =>
      loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *;
          first [pose proof FRSEG as XFRSEG | pose proof I as XFRSEG]; first [pose proof SP0W as XSP0W | pose proof I as XSP0W]; first [pose proof FRSH as XFRSH | pose proof I as XFRSH];
          clear - Hx FRHI LOW LOR FR64 FR0 SP0R1 SP0R0 XFRSEG XSP0W XFRSH;
          unfold parked, hid in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end).
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => unfold parked in FCD, CKH, FRSH; unfold shad, SHB in *; clear - Hx FCD CKH FRSH FRHI SP0R0 SP0R1 CKR LOW LOR FR64 FR0; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
      carry_mu MUx PXD ltac:(fun Hx => unfold parked in FCD1, CKH1, FRSH; unfold shad, SHB in *; clear - Hx FCD1 CKH1 FRSH FRHI SP0R0 SP0R1 CKR1 LOW LOR FR64 FR0; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    hide PXS. hide PXD.
    repeat match goal with H : parked _ |- _ => hide H end.
    join_cells FRM FRMr.
    idtac "MARK carried x".
    frame_release_g RT AF GP MST Σ fr 2%nat 256 PF AGF PFS usp lo 0x9df70
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => agf_side PFS NFA LOR Hx) ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
    idtac "MARK frame released".
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    lazymatch goal with MUx : munch [(?fl, ?fl + 1)] _ ?mb |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => repeat match goal with Hf : fl < pix \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx PXD ltac:(fun Hx => repeat match goal with Hf : fl < pixd \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia) end.
    hide PXS. hide PXD.
    clear_acc. refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -208) |- _ => release_frame FR ST' usp end.
    lazymatch goal with MUx : munch _ _ ?mb |- evt _ _ (MS _ _ _ _ _ ?mb _) =>
      carry_mu MUx PXS ltac:(fun Hx => clear - Hx CKR LOW LOR; repeat split; try exact I; lia);
      carry_mu MUx PXD ltac:(fun Hx => clear - Hx CKR1 LOW LOR; repeat split; try exact I; lia) end.
    cps_stop.
    idtac "MARK epilogue walked".
    apply cps_finish; intros c Hc; subst QF; unfold dbin_post; cbv beta.
    set (vf := pv_inf (pv_res v1 v) v).
    assert (VFC : p_cmap vf = 0) by (exact VCMAP).
    assert (VFD : p_data vf = dat) by reflexivity.
    unfold hid in HOKD.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, pixd, vf, (mkCmapv 0 0 0 0) end.
    split.
    2: {
    split; [intros Z0; exfalso; clear - Z0 PD0; lia|].
    split.
    { intros _. rewrite LV2, LVZ.
      pose proof (live_destroy_tmpl (rt_live RT Σ) pixd dat rs 0 0 0 vf (mkCmapv 0 0 0 0) VFD VFC
                    (fun N => False_ind _ (N eq_refl)) VDATA1 ltac:(unfold parked in DDNE; exact DDNE) (fun N => False_ind _ (N eq_refl))
                    (fun e He => conj (SUBP' e He) (SUBD' e He)) (fun N => False_ind _ (N eq_refl))) as LD.
      cbn [Z.eqb] in LD. exact LD. }
    split.
    { intros p n Hp. rewrite LV2, LVZ in Hp. cbn [In] in Hp. destruct Hp as [Hp|[Hp|Hp]]; [injection Hp as <- <-; exact DDN| injection Hp as <- <-; clear; lia| exact (LVP p n Hp)]. }
    split; [rewrite LV2, LVZ; cbn [length]; clear; lia|].
    split; [exact FRS2|]. split; [rewrite SP2; exact SP0z|].
    unfold DBIN_COST, OP_COST, is_d8. cbn [Z.eqb Pos.eqb].
    rewrite CR2. clear - CRz. unfold RASTER_COST in *. lia.
    }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    split; [unfold lpost_f, rt_after_f; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); split; [split; [assumption| split; assumption]| split; assumption]|].
    split; [unfold keepsL, rt_pres_fp; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
    split.
    { rewrite LV2, LVZ. lazymatch goal with PS : rw_cells asegs ?mc pix _ |- pix_obj _ ?mc _ _ _ =>
        exact (PSRC ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) 1 mc ltac:(intros e He; right; right; exact He) AGF PS) end. }
    right. split; [| rewrite VFD; exact VDATA1].
    rewrite LV2, LVZ.
    split; [unfold pix_cells, vf, pv_inf, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP; exact PXD|].
    split; [split; [right; left; reflexivity| split; [exact PD0| split; [exact PD16| clear; lia]]]|].
    split; [exact HOKD|].
    split; [right; split; [split; [left; reflexivity| split; [exact DD0| split; [exact DD16| exact DDN]]]| unfold parked in DDNE; exact DDNE]| left; exact VFC].
  - (* [comment removed for export] *)
    specialize (LVP1 CMN). clear LVP0.
    set (dtt := p_data vt) in *. set (rst := rsize vt) in *.
    assert (LVPB : rt_live RT Σp = (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVP1, LVI; reflexivity).
    assert (LSUBp : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σp)) by (intros e He; rewrite LVPB; do 4 right; exact He).
    assert (LVPi : forall e, In e (rt_live RT Σi) -> In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ)) by (intros e He; rewrite <- LVI; exact He).
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
    assert (NCT : forall a, PF a -> a < pixt \/ pixt + 64 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σp _ pixt 64 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTP PTIN ltac:(intros e He; exact (SUBT e ltac:(right; right; exact He))));
          [ rewrite FRSp; intros e He; right; exact He | rewrite SP0p; ul | exact (proj1 Ha) ]).
    assert (NCDT : forall a, PF a -> a < dtt \/ dtt + rst <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σp _ dtt rst (rt_live RT Σ) (rt_frames RT Σ) usp a ARTP DTIN ltac:(intros e He; exact (SUBDT e ltac:(right; right; exact He))));
          [ rewrite FRSp; intros e He; right; exact He | rewrite SP0p; ul | exact (proj1 Ha) ]).
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
      pose proof (live_apart2 RT AF Σp mm pixt 64 dtt rst A PTIN DTIN ltac:(intros E; injection E; intros _ E1; unfold parked in DTNE; exact (DTNE (eq_sym E1)))) as DTT end.
    hide POT. hide POSp. hide HOKT. hide SUBT. hide SUBDT.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK arm B start".
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9de1c].
    idtac "MARK arm B at calloc 1".
    assert (WPLO : 0 < p_wpl vt) by (rewrite EWS; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    assert (WPHI : p_wpl vt <= 5001) by (rewrite EWS; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    rewrite !(sx32_small (p_wpl vt)) by (clear - WPLO WPHI; lia).
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 1".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc1 : In (0x9dd7c :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT Σp _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -208) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -208) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP2; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := p_wpl vt) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRc1]
           | |- _ => first [ unfold CALLOC_MAX; clear - WPLO WPHI; lia
                           | rewrite LVPB; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                           | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
           end. }
    idtac "MARK calloc 1 applied".
    clear UCC.
    after_call RT AF.
    fold_pres usp.
    idtac "MARK after calloc 1".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σb1; rename A into ARTB1 end.
    lazymatch goal with H : rt_live RT Σb1 = (?p, _) :: _ |- _ => rename H into LVB1N; rename p into bufs1 end.
    lazymatch goal with H : rw_cells asegs _ bufs1 [CB _ _] |- _ => rename H into B1Z end.
    assert (LVB1 : rt_live RT Σb1 = (bufs1, p_wpl vt * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVB1N, LVPB; reflexivity).
    assert (FRSb1 : rt_frames RT Σb1 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σb1 = _ |- _ => rewrite E end; exact FRSp).
    assert (SP0b1 : rt_sp0 RT Σb1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRb1 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σb1) by (repeat match goal with E : rt_credit RT Σb1 = _ |- _ => rewrite E end; exact CRp).
    lazymatch goal with H : 0 < bufs1 |- _ => rename H into B10 end.
    lazymatch goal with H : bufs1 mod 16 = 0 |- _ => rename H into B116 end.
    chunk_facts RT AF GP bufs1 (p_wpl vt * 4). fframe_chunk RT AF fr 2%nat 256 bufs1 (p_wpl vt * 4).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9de1c].
    idtac "MARK arm B at calloc 2".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 2".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc2 : In (0x9dd8c :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -208) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -208) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP2; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := p_wpl vt) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRc2]
           | |- _ => first [ unfold CALLOC_MAX; clear - WPLO WPHI; lia
                           | rewrite LVB1; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                           | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
           end. }
    idtac "MARK calloc 2 applied".
    clear UCC.
    after_call RT AF.
    fold_pres usp.
    idtac "MARK after calloc 2".
    try forget_junk FR; try forget_junk FRM; try forget_junk FSH; try forget_junk FRMb.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σb2; rename A into ARTB2 end.
    lazymatch goal with H : rt_live RT Σb2 = (?p, _) :: _ |- _ => rename H into LVB2N; rename p into bufs2 end.
    lazymatch goal with H : rw_cells asegs _ bufs2 [CB _ _] |- _ => rename H into B2Z end.
    assert (LVB2 : rt_live RT Σb2 = (bufs2, p_wpl vt * 4) :: (bufs1, p_wpl vt * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVB2N, LVB1; reflexivity).
    assert (FRSb2 : rt_frames RT Σb2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σb2 = _ |- _ => rewrite E end; exact FRSb1).
    assert (SP0b2 : rt_sp0 RT Σb2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRb2 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σb2) by (repeat match goal with E : rt_credit RT Σb2 = _ |- _ => rewrite E end; exact CRb1).
    lazymatch goal with H : 0 < bufs2 |- _ => rename H into B20 end.
    lazymatch goal with H : bufs2 mod 16 = 0 |- _ => rename H into B216 end.
    chunk_facts RT AF GP bufs2 (p_wpl vt * 4). fframe_chunk RT AF fr 2%nat 256 bufs2 (p_wpl vt * 4).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_ditherToBinaryLow; 0x9de5c].
    idtac "MARK arm B at ditherToBinaryLow".
    rewrite ?(sx32_small (p_w v)) by (clear - HW0 HW2; lia). rewrite ?(sx32_small (p_h v)) by (clear - HH0 HH2; lia).
    assert (WPLD1 : 0 < p_wpl v1) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    assert (WPLD2 : p_wpl v1 <= 626) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    rewrite ?(sx32_small (p_wpl v1)) by (clear - WPLD1 WPLD2; lia).
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call DLOW".
    (* [comment removed for export] *)
    assert (NEB2 : forall e, In e ((bufs1, p_wpl vt * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> bufs2)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σb2 _ [] bufs2 (p_wpl vt * 4) _ e ARTB2 LVB2); [cbn [app]; exact He| clear - WPLO; lia| exact Hn]).
    assert (NEB1 : forall e, In e ((dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> bufs1)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σb1 _ [] bufs1 (p_wpl vt * 4) _ e ARTB1 LVB1); [cbn [app]; exact He| clear - WPLO; lia| exact Hn]).
    assert (SUBB1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σb1) /\ fst e <> bufs1)
      by (intros e He; split; [rewrite LVB1; do 5 right; exact He| apply NEB1; [do 4 right; exact He| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBB2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σb2) /\ fst e <> bufs2)
      by (intros e He; split; [rewrite LVB2; do 6 right; exact He| apply NEB2; [do 5 right; exact He| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (NCB1 : forall a, PF a -> a < bufs1 \/ bufs1 + p_wpl vt * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σb1 _ bufs1 (p_wpl vt * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTB1 ltac:(rewrite LVB1; left; reflexivity) SUBB1);
          [ rewrite FRSb1; intros e He; right; exact He | rewrite SP0b1; ul | exact (proj1 Ha) ]).
    assert (NCB2 : forall a, PF a -> a < bufs2 \/ bufs2 + p_wpl vt * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σb2 _ bufs2 (p_wpl vt * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTB2 ltac:(rewrite LVB2; left; reflexivity) SUBB2);
          [ rewrite FRSb2; intros e He; right; exact He | rewrite SP0b2; ul | exact (proj1 Ha) ]).
    assert (ND4 : NoDup [dat; dtt; bufs1; bufs2]).
    { pose proof (NEB2 (dat, rs) ltac:(do 3 right; left; reflexivity) DDN) as Q1. pose proof (NEB2 (bufs1, p_wpl vt * 4) ltac:(left; reflexivity) ltac:(cbn [snd]; clear - WPLO; lia)) as Q2.
      pose proof (NEB2 (dtt, rst) ltac:(right; left; reflexivity) DTN) as Q3.
      pose proof (NEB1 (dat, rs) ltac:(do 2 right; left; reflexivity) DDN) as Q4. pose proof (NEB1 (dtt, rst) ltac:(left; reflexivity) DTN) as Q5.
      cbn [fst] in Q1, Q2, Q3, Q4, Q5. unfold parked in NDDT. clear - Q1 Q2 Q3 Q4 Q5 NDDT.
      nodup4. }
    idtac "MARK DLOW facts".
    eapply cps_seq.
    { pose proof (ditherToBinaryLow_ok RT AF GP RC) as DL; unfold ditherToBinaryLow_cps in DL;
      eapply DL with (lo := lo) (datad := dat) (w := p_w v) (h := p_h v) (wpld := p_wpl v1) (datas := dtt) (wpls := p_wpl vt) (bufs1 := bufs1) (bufs2 := bufs2); clear DL.
      all: lazymatch goal with
           | |- fdfs_only _ => exact FDO
           | |- mat_stable _ => exact MST
           | |- s32 _ _ => split; [| reflexivity]; first [clear - HW0 HW2; lia | clear - HH0 HH2; lia | clear - WPLD1 WPLD2; lia | clear - WPLO WPHI; lia]
           | |- @eq word _ _ => reflexivity
           | |- (0 < _ <= 20000) => first [clear - HW0 HW2; lia | clear - HH0 HH2; lia]
           | |- _ = (_ + 31) / 32 => first [rewrite EWD; reflexivity | rewrite EWS; reflexivity]
           | |- 4 * _ <= _ => first [clear - RSTB1; lia | clear - RSTB; lia]
           | |- chunk _ _ (4 * (_ * _)) => first [ split; [rewrite LVB2, ERS; do 4 right; left; reflexivity| split; [exact DD0| split; [exact DD16| rewrite ERS in DDN; exact DDN]]]
                                                 | split; [rewrite LVB2, ERST; do 2 right; left; reflexivity| split; [exact DT0| split; [exact DT16| rewrite ERST in DTN; exact DTN]]] ]
           | |- chunk _ _ (4 * _) => first [ split; [rewrite LVB2; right; left; f_equal; clear; lia| split; [exact B10| split; [exact B116| clear - WPLO; lia]]]
                                           | split; [rewrite LVB2; left; f_equal; clear; lia| split; [exact B20| split; [exact B216| clear - WPLO; lia]]] ]
           | |- NoDup _ => exact ND4
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => unfold lres; rewrite FRSb2, LVB2; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split;
                                   [clear - FRB; lia| clear - LVB; lia| clear - CRb2 CRB; unfold RASTER_COST in *; lia
                                   | intros p n Hp; destruct Hp as [E|[E|[E|[E|[E|[E|Hp]]]]]];
                                     [injection E; intros <- <-; clear - WPLO; lia | injection E; intros <- <-; clear - WPLO; lia | injection E; intros <- <-; exact DTN | injection E; intros <- <-; clear; lia
                                     | injection E; intros <- <-; exact DDN | injection E; intros <- <-; clear; lia | exact (LVP p n Hp)]]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK DLOW applied".
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT Σb2 ?mm |- _ =>
      pose proof (live_apart2 RT AF Σb2 mm pix 64 bufs1 (p_wpl vt * 4) A ltac:(rewrite LVB2; do 6 right; exact PIN) ltac:(rewrite LVB2; right; left; reflexivity)
                    ltac:(intros E; injection E; intros _ E1; exact (NEB1 (pix, 64) ltac:(do 4 right; exact PIN) ltac:(cbn; clear; lia) E1))) as APS1;
      pose proof (live_apart2 RT AF Σb2 mm pix 64 bufs2 (p_wpl vt * 4) A ltac:(rewrite LVB2; do 6 right; exact PIN) ltac:(rewrite LVB2; left; reflexivity)
                    ltac:(intros E; injection E; intros _ E1; exact (NEB2 (pix, 64) ltac:(do 5 right; exact PIN) ltac:(cbn; clear; lia) E1))) as APS2;
      pose proof (live_apart2 RT AF Σb2 mm pixd 64 bufs1 (p_wpl vt * 4) A ltac:(rewrite LVB2; do 5 right; left; reflexivity) ltac:(rewrite LVB2; right; left; reflexivity)
                    ltac:(intros E; injection E; intros _ E1; exact (NEB1 (pixd, 64) ltac:(do 3 right; left; reflexivity) ltac:(cbn; clear; lia) E1))) as APD1;
      pose proof (live_apart2 RT AF Σb2 mm pixd 64 bufs2 (p_wpl vt * 4) A ltac:(rewrite LVB2; do 5 right; left; reflexivity) ltac:(rewrite LVB2; left; reflexivity)
                    ltac:(intros E; injection E; intros _ E1; exact (NEB2 (pixd, 64) ltac:(do 4 right; left; reflexivity) ltac:(cbn; clear; lia) E1))) as APD2;
      pose proof (live_apart2 RT AF Σb2 mm pixt 64 bufs1 (p_wpl vt * 4) A ltac:(rewrite LVB2; do 3 right; left; reflexivity) ltac:(rewrite LVB2; right; left; reflexivity)
                    ltac:(intros E; injection E; intros _ E1; exact (NEB1 (pixt, 64) ltac:(right; left; reflexivity) ltac:(cbn; clear; lia) E1))) as APT1;
      pose proof (live_apart2 RT AF Σb2 mm pixt 64 bufs2 (p_wpl vt * 4) A ltac:(rewrite LVB2; do 3 right; left; reflexivity) ltac:(rewrite LVB2; left; reflexivity)
                    ltac:(intros E; injection E; intros _ E1; exact (NEB2 (pixt, 64) ltac:(do 2 right; left; reflexivity) ltac:(cbn; clear; lia) E1))) as APT2;
      pose proof (live_apart2 RT AF Σb2 mm pixt 64 dat rs A ltac:(rewrite LVB2; do 3 right; left; reflexivity) ltac:(rewrite LVB2; do 4 right; left; reflexivity)
                    ltac:(intros E; injection E; intros _ E1; unfold parked in NDT; exact (NDT (eq_sym E1)))) as APT0 end.
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT.
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [solve [find_in]| exact Hx])
                    ltac:(fun Hx => unfold parked in APT0; clear - Hx APT0 APT1 APT2 ERS; lia);
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => fr_side fr Hx);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => sh_side fr FR64 Hx);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx])
                    ltac:(fun Hx => unfold parked in DPD; clear - Hx DPD APD1 APD2 ERS; lia);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx])
                    ltac:(fun Hx => unfold parked in DSD; clear - Hx DSD APS1 APS2 ERS; lia) end.
    idtac "MARK carried".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; pose proof (NCD _ (conj Hx1 Hx2)) as Y1; pose proof (NCB1 _ (conj Hx1 Hx2)) as Y2; pose proof (NCB2 _ (conj Hx1 Hx2)) as Y3;
                              clear - Y1 Y2 Y3 ERS; repeat split; try exact I; lia).
    idtac "MARK after DLOW".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σd; rename A into ARTD end.
    assert (LVD : rt_live RT Σd = (bufs2, p_wpl vt * 4) :: (bufs1, p_wpl vt * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σd = _ |- _ => rewrite E end; exact LVB2).
    assert (FRSd : rt_frames RT Σd = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σd = _ |- _ => rewrite E end; exact FRSb2).
    assert (SP0d : rt_sp0 RT Σd = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRd : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σd) by (lazymatch goal with E : rt_credit RT Σb2 <= rt_credit RT Σd |- _ => clear - E CRb2; lia end).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9de5c].
    idtac "MARK arm B at free 1".

    assert (NPB1 : pixd <> bufs1) by (exact (NEB1 (pixd, 64) ltac:(do 3 right; left; reflexivity) ltac:(cbn; clear; lia))).
    assert (NPB2 : pixd <> bufs2) by (exact (NEB2 (pixd, 64) ltac:(do 4 right; left; reflexivity) ltac:(cbn; clear; lia))).
    assert (NSB1 : pix <> bufs1) by (exact (NEB1 (pix, 64) ltac:(do 4 right; exact PIN) ltac:(cbn; clear; lia))).
    assert (NSB2 : pix <> bufs2) by (exact (NEB2 (pix, 64) ltac:(do 5 right; exact PIN) ltac:(cbn; clear; lia))).
    assert (NB21 : bufs2 <> bufs1) by (intros E; apply (NEB2 (bufs1, p_wpl vt * 4) ltac:(left; reflexivity) ltac:(cbn; clear - WPLO; lia)); symmetry; exact E).
    assert (NRB1 : forall e, In e ((dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> bufs1)
      by (intros e He; apply (NEB1 e He); destruct He as [<-|[<-|[<-|[<-|He]]]]; [exact DTN| cbn; clear; lia| exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (NRB2 : forall e, In e ((dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> bufs2)
      by (intros e He; apply (NEB2 e); [right; exact He|]; destruct He as [<-|[<-|[<-|[<-|He]]]]; [exact DTN| cbn; clear; lia| exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    park_ne.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call free 1".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf1 : In (0x9ddcc :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -208) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -208) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP2; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := bufs1) (n := p_wpl vt * 4); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVD; right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf1]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK free 1 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf1; rename A into ARTF1 end.
    assert (LVF1 : rt_live RT Σf1 = (bufs2, p_wpl vt * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf1 = _ |- _ => rewrite E end; rewrite LVD; unfold parked in NB21; exact (live_remove_2nd bufs1 _ bufs2 _ _ NB21 NRB1)).
    assert (FRSf1 : rt_frames RT Σf1 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf1 = _ |- _ => rewrite E end; exact FRSd).
    assert (SP0f1 : rt_sp0 RT Σf1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf1 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σf1) by (repeat match goal with E : rt_credit RT Σf1 = _ |- _ => rewrite E end; exact CRd).
    assert (LSUBf1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf1)) by (intros e He; rewrite LVF1; do 5 right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [rewrite LVF1; do 4 right; left; reflexivity| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [rewrite LVF1; do 5 right; exact PIN| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [rewrite LVF1; do 2 right; left; reflexivity| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK carried f1".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf1| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9de5c].
    idtac "MARK arm B at free 2".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf2 : In (0x9ddd4 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -208) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -208) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP2; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := bufs2) (n := p_wpl vt * 4); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVF1; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf2]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK free 2 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf2; rename A into ARTF2 end.
    assert (LVF2 : rt_live RT Σf2 = (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf2 = _ |- _ => rewrite E end; rewrite LVF1; exact (live_remove_hd bufs2 _ _ NRB2)).
    assert (FRSf2 : rt_frames RT Σf2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf2 = _ |- _ => rewrite E end; exact FRSf1).
    assert (SP0f2 : rt_sp0 RT Σf2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf2 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σf2) by (repeat match goal with E : rt_credit RT Σf2 = _ |- _ => rewrite E end; exact CRf1).
    assert (LSUBf2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf2)) by (intros e He; rewrite LVF2; do 4 right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [rewrite LVF2; do 3 right; left; reflexivity| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [rewrite LVF2; do 4 right; exact PIN| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [rewrite LVF2; right; left; reflexivity| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK carried f2".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf2| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDestroy; 0x9de5c].
    idtac "MARK arm B at pixDestroy".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call DES".
    split_at FRM 10%nat PPC. split_at PPC 1%nat FRMb.
    pose proof FSH as SH10. split_at SH10 10%nat SH10b. split_at SH10b 1%nat SH10c. clear SH10 SH10c.
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    unfold hid in HOKT.
    lazymatch goal with PT : rw_cells asegs ?mc pixt _ |- cps _ (ASTA RT Σf2 _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (POT4 : pix_obj (rt_live RT Σf2) mc pixt vt (mkCmapv 0 0 0 0))
        by (split; [unfold pix_cells; rewrite WT, HT, DT, CMT; fold dtt; exact PT|]; split; [split; [rewrite LVF2; right; left; reflexivity| split; [exact PT0| split; [exact PT16| clear; lia]]]|];
            split; [exact HOKT|]; split; [right; split; [split; [rewrite LVF2; left; reflexivity| split; [exact DT0| split; [exact DT16| exact DTN]]]| unfold parked in DTNE; exact DTNE]| left; exact CMT]);
      assert (OPP : optrL RT (live_destroy pixt vt (mkCmapv 0 0 0 0) (rt_live RT Σf2)) Σf2 mc (fr + 80) 8)
        by (unfold optrL, accok; split;
            [ right; exists fr, 2%nat; rewrite FRSf2; change (fs_size 2) with 256;
              split; [left; reflexivity|]; split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FR0; lia|];
              split; [clear - FRHI SP0R1; lia|];
              replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
              destruct SH10b as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B
            | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; unfold SEGTOP_A; split; [clear - FRSH; unfold parked in FRSH; lia| clear - FRSEG; unfold parked in FRSEG; lia] ]);
      assert (UCC : chain_ok mc (usp + -208) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -208) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP2; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    hide HOKT. clear FRrec2.
    idtac "MARK destroy args".
    assert (CR1 : 1 <= rt_credit RT Σf2) by (clear - CRf2 CRB; unfold RASTER_COST in *; lia).
    eapply cps_seq.
    {
    eapply DES with (lo := lo) (pp := fr + 80) (pix := pixt) (v := vt) (cv := mkCmapv 0 0 0 0) (ras := bv_unsigned ra :: ras).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - exact OPP.
    - exact PPC.
    - exact POT4.
    - unfold uctx. rewrite !unsigned_lit by (clear - USP0 USP1 LOR STa; lia). exact UCC.
    - rewrite RAF, RAS. unfold DESTROY_FREE_RAS, RA_FUZZ_OP2, RA_TOP. rewrite unsigned_lit by (clear; lia).
      repeat (apply Forall_cons; [apply ct_mem_In; vm_compute; reflexivity |]). apply Forall_nil.
    - lenv_tac.
    - unfold lres; rewrite FRSf2, LVF2; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [clear - FRB; lia| clear - LVB; lia| exact CR1|
        intros p n Hp; destruct Hp as [E|[E|[E|[E|Hp]]]]; [injection E; intros <- <-; exact DTN | injection E; intros <- <-; clear; lia | injection E; intros <- <-; exact DDN | injection E; intros <- <-; clear; lia | exact (LVP p n Hp)]].
    }
    idtac "MARK DES applied".
    clear POT4 OPP UCC CR1 SH10b.
    hide FRM. hide FRMb. hide FSH. hide PXD. hide PXS.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σz; rename A into ARTZ end.
    unfold hid in SUBT, SUBDT.
    assert (LVZ : rt_live RT Σz = (dat, rs) :: (pixd, 64) :: rt_live RT Σ).
    { repeat match goal with E : rt_live RT Σz = _ |- _ => rewrite E end. rewrite LVF2.
      pose proof (live_destroy_tmpl ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) pixt dtt rst 0 0 0 vt (mkCmapv 0 0 0 0) eq_refl CMT
                    (fun N => False_ind _ (N eq_refl)) ltac:(clear - DT0; lia) ltac:(unfold parked in DTNE; exact DTNE) (fun N => False_ind _ (N eq_refl))
                    (fun e He => conj (proj2 (SUBT e He)) (proj2 (SUBDT e He))) (fun N => False_ind _ (N eq_refl))) as LD.
      cbn [Z.eqb] in LD. exact LD. }
    assert (FRSz : rt_frames RT Σz = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σz = _ |- _ => rewrite E end; exact FRSf2).
    assert (SP0z : rt_sp0 RT Σz = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRz : rt_credit RT Σ - (2 * RASTER_COST + 26) <= rt_credit RT Σz) by (lazymatch goal with E : rt_credit RT Σf2 - 1 <= rt_credit RT Σz |- _ => clear - E CRf2; lia end).
    assert (LSUBz : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σz)) by (intros e He; rewrite LVZ; right; right; exact He).
    hide SUBT. hide SUBDT.
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => clear - Hx; lia);
      carry AGx FRMb ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => clear - Hx; lia);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia])
                    ltac:(fun Hx => unfold parked in FRSH; unfold shad, SHB in *; clear - Hx FR64 FRSH; first [lia | Z.div_mod_to_equations; lia]);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [rewrite LVZ; right; left; reflexivity| exact Hx]) ltac:(fun Hx => unfold parked in FCD1; clear - Hx FCD1; lia);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [rewrite LVZ; right; right; exact PIN| exact Hx]) ltac:(fun Hx => unfold parked in FCD; clear - Hx FCD; lia) end.
    idtac "MARK carried z".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; destruct (NFA _ (conj Hx1 Hx2)) as [N1 N2]; clear - N1; repeat split; try exact I; lia).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    (* [comment removed for export] *)
    unfold hid in SUBP, SUBD.
    assert (SUBP' : forall e, In e (rt_live RT Σ) -> fst e <> pixd) by (intros e He; exact (proj2 (SUBP e He))).
    assert (SUBD' : forall e, In e (rt_live RT Σ) -> fst e <> dat) by (intros e He; exact (proj2 (SUBD e He))).
    clear SUBP SUBD.
    assert (PDINz : In (pixd, 64) (rt_live RT Σz)) by (rewrite LVZ; right; left; reflexivity).
    assert (DDINz : In (dat, rs) (rt_live RT Σz)) by (rewrite LVZ; left; reflexivity).
    assert (PINz : In (pix, 64) (rt_live RT Σz)) by (rewrite LVZ; right; right; exact PIN).
    assert (DINz : In (p_data v, 4 * (p_wpl v * p_h v)) (rt_live RT Σz)) by (rewrite LVZ; right; right; exact DIN).
    sigma_gc RT Σ Σz.
    repeat match goal with H : In (?b, _) (rt_live RT Σ) |- _ => lazymatch b with pix => fail | p_data v => fail | _ => clear H end end.
    idtac "MARK diet".
    try forget_junk FR; try forget_junk FRM; try forget_junk FSH; try forget_junk FRMb.
    hide PXS. hide PXD.
    (* [comment removed for export] *)
    repeat match goal with H : context [bufs1] |- _ => clear H end.
    repeat match goal with H : context [bufs2] |- _ => clear H end.
    try clear bufs1. try clear bufs2.
    repeat match goal with H : wmono _ _ ?b |- _ => lazymatch goal with |- context [b] => fail | _ => clear H end end.
    repeat match goal with H : munch _ _ ?b |- _ => lazymatch goal with |- context [b] => fail | _ => clear H end end.
    clear_acc.
    hide FCD. hide FCS. hide CKH. hide FCD1. hide FCS1. hide CKH1. hide DDNE. hide VDATA1. hide FRSH.
    repeat match goal with H : parked ?T |- _ => lazymatch T with context [fr] => hide H | _ => clear H end end.
    unfold hid in FRSH. unfold parked in FRSH.
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9debc].
    idtac "MARK at flag load".
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    idtac "MARK at pokes".
    try unfold hid in FRM. try unfold hid in FSH. split_at FRM 1%nat FRMr.
    Time (eapply evt_cut;
    [ eapply EVQ_exit;
      [ eapply dbin_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
      | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
    | ]).
    clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold dbin_exit_W, SHB in MUx. unfold dbin_sh_f5 in FSH.
    idtac "MARK pokes applied".
    Time loop_art RT AF Σz mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    Time (lazymatch type of MUx with munch _ ?ma ?mb =>
      loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *;
          first [pose proof FRSEG as XFRSEG | pose proof I as XFRSEG]; first [pose proof SP0W as XSP0W | pose proof I as XSP0W]; first [pose proof FRSH as XFRSH | pose proof I as XFRSH];
          clear - Hx FRHI LOW LOR FR64 FR0 SP0R1 SP0R0 XFRSEG XSP0W XFRSH;
          unfold parked, hid in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end).
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => unfold parked in FCD, CKH, FRSH; unfold shad, SHB in *; clear - Hx FCD CKH FRSH FRHI SP0R0 SP0R1 CKR LOW LOR FR64 FR0; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
      carry_mu MUx PXD ltac:(fun Hx => unfold parked in FCD1, CKH1, FRSH; unfold shad, SHB in *; clear - Hx FCD1 CKH1 FRSH FRHI SP0R0 SP0R1 CKR1 LOW LOR FR64 FR0; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    hide PXS. hide PXD.
    repeat match goal with H : parked _ |- _ => hide H end.
    join_cells FRM FRMr.
    idtac "MARK carried x".
    frame_release_g RT AF GP MST Σ fr 2%nat 256 PF AGF PFS usp lo 0x9df70
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => agf_side PFS NFA LOR Hx) ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
    idtac "MARK frame released".
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    lazymatch goal with MUx : munch [(?fl, ?fl + 1)] _ ?mb |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => repeat match goal with Hf : fl < pix \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx PXD ltac:(fun Hx => repeat match goal with Hf : fl < pixd \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia) end.
    hide PXS. hide PXD.
    clear_acc. refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 272, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -208) |- _ => release_frame FR ST' usp end.
    lazymatch goal with MUx : munch _ _ ?mb |- evt _ _ (MS _ _ _ _ _ ?mb _) =>
      carry_mu MUx PXS ltac:(fun Hx => clear - Hx CKR LOW LOR; repeat split; try exact I; lia);
      carry_mu MUx PXD ltac:(fun Hx => clear - Hx CKR1 LOW LOR; repeat split; try exact I; lia) end.
    cps_stop.
    idtac "MARK epilogue walked".
    apply cps_finish; intros c Hc; subst QF; unfold dbin_post; cbv beta.
    set (vf := pv_inf (pv_res v1 v) v).
    assert (VFC : p_cmap vf = 0) by (exact VCMAP).
    assert (VFD : p_data vf = dat) by reflexivity.
    unfold hid in HOKD.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, pixd, vf, (mkCmapv 0 0 0 0) end.
    split.
    2: {
    split; [intros Z0; exfalso; clear - Z0 PD0; lia|].
    split.
    { intros _. rewrite LV2, LVZ.
      pose proof (live_destroy_tmpl (rt_live RT Σ) pixd dat rs 0 0 0 vf (mkCmapv 0 0 0 0) VFD VFC
                    (fun N => False_ind _ (N eq_refl)) VDATA1 ltac:(unfold parked in DDNE; exact DDNE) (fun N => False_ind _ (N eq_refl))
                    (fun e He => conj (SUBP' e He) (SUBD' e He)) (fun N => False_ind _ (N eq_refl))) as LD.
      cbn [Z.eqb] in LD. exact LD. }
    split.
    { intros p n Hp. rewrite LV2, LVZ in Hp. cbn [In] in Hp. destruct Hp as [Hp|[Hp|Hp]]; [injection Hp as <- <-; exact DDN| injection Hp as <- <-; clear; lia| exact (LVP p n Hp)]. }
    split; [rewrite LV2, LVZ; cbn [length]; clear; lia|].
    split; [exact FRS2|]. split; [rewrite SP2; exact SP0z|].
    unfold DBIN_COST, OP_COST, is_d8. cbn [Z.eqb Pos.eqb].
    rewrite CR2. clear - CRz. unfold RASTER_COST in *. lia.
    }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    split; [unfold lpost_f, rt_after_f; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); split; [split; [assumption| split; assumption]| split; assumption]|].
    split; [unfold keepsL, rt_pres_fp; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
    split.
    { rewrite LV2, LVZ. lazymatch goal with PS : rw_cells asegs ?mc pix _ |- pix_obj _ ?mc _ _ _ =>
        exact (PSRC ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) 1 mc ltac:(intros e He; right; right; exact He) AGF PS) end. }
    right. split; [| rewrite VFD; exact VDATA1].
    rewrite LV2, LVZ.
    split; [unfold pix_cells, vf, pv_inf, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP; exact PXD|].
    split; [split; [right; left; reflexivity| split; [exact PD0| split; [exact PD16| clear; lia]]]|].
    split; [exact HOKD|].
    split; [right; split; [split; [left; reflexivity| split; [exact DD0| split; [exact DD16| exact DDN]]]| unfold parked in DDNE; exact DDNE]| left; exact VFC].
Qed.
End DBINC.
