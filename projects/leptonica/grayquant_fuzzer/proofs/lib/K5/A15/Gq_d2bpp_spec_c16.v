(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Lept_chain Lept_gmax_defs
  Gm_iface Gq_obj Gq_iface Gq_dbin_defs Gq_d2bpp_defs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Lept_fuzzkit Lept_deserkit Gm_kit Gm_livekit Gm_livekit2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Gq_dt2tab Gq_dither2_l1 Gq_dither2_rows Gq_cmaplin Gq_d2bpp_kit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Gq_d2bpp_exit.
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
Local Ltac park_ne := repeat match goal with H : (?a <> ?b) |- _ => lazymatch type of a with Z => change (a <> b) with (parked (a <> b)) in H end end.

Section D2C.
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
Hypothesis PSC : pixSetColormap_cps RT.

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
Local Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ ?m ?B ?cs2 =>
    let J := fresh "J" in
    assert (J : rw_cells asegs m A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app m A cs1 cs2)); split;
          [ exact H1
          | cbn [cells_size csize Nat.add]; lazymatch goal with |- rw_cells _ _ ?X _ => replace X with B by lia end; exact H2 ]);
    clear H1 H2; cbn [app] in J; rename J into H1 end end.
(* [comment removed for export] *)
Local Ltac cside p Hx K1 K2 K3 K4 K5 K6 K7 :=
  repeat match goal with Hf : parked ?T |- _ => lazymatch T with context [p] => unfold parked in Hf; revert Hf end end;
  repeat match goal with Hr : p + _ <= rt_sp0 _ _ - _ |- _ => revert Hr end;
  unfold shad, SHB in *; clear - Hx K1 K2 K3 K4 K5 K6 K7; intros; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
(* [comment removed for export] *)
Local Ltac forget_junk H :=
  repeat match type of H with context [CB _ ?bs] =>
    lazymatch bs with
    | firstn _ _ => let j := fresh "jq" in set (j := bs) in *; clearbody j
    | skipn _ _ => let j := fresh "jq" in set (j := bs) in *; clearbody j
    end end.

(* [comment removed for export] *)
Local Ltac forget_cells H k n :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let pre := list_firstn k cs in let rest := list_skipn k cs in let mid := list_firstn n rest in let post := list_skipn n rest in
    change cs with (pre ++ mid ++ post) in H; apply (rw_cells_merge asegs m A pre mid post) in H;
    cbn [cells_size csize cells_bytes cbytes Nat.add app] in H end.
(* [comment removed for export] *)
Local Ltac por := first [ assumption
  | match goal with H : parked (?B \/ ?A) |- ?A \/ ?B => unfold parked in H; clear - H; tauto end
  | lia | Z.div_mod_to_equations; lia ].

(* [comment removed for export] *)
Local Ltac sigma_gc RT S0 Sx :=
  repeat match goal with S : rts RT |- _ =>
    tryif constr_eq S S0 then fail else tryif constr_eq S Sx then fail else
      (repeat match goal with H : context [S] |- _ => clear H end; clear S) end.

Local Ltac eqv :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity.

Lemma d2bpp_spec_c16 : d2bpp_spec_case RT 16.
Proof using AF GP RC RERR PCS PCR PCI PRC PDR DES CML PSC.
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
  (* [comment removed for export] *)
  park_disj. park_ne.
  carve_frame 304%nat ST.
  walk_to AF MST [(usp - 304, usp)] [e_stack_malloc 2%nat].
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
  walk_to AF MST [(usp - 304, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9df10].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx => agf_side PFS NFA LOR Hx) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH. local_acc FSH fr 8%nat 64 FR64 FR1 ACCD.
  park_disj.
  idtac "MARK header done".
  try forget_junk FR; try forget_junk FRM; try forget_junk FSH.
  walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCreate; 0x9dfb8; 0x9df80; 0x9df48; e_stack_malloc 2%nat].
  idtac "MARK after dims".
  rewrite D8. brF.
  awalk [e_pixCreate; 0x9df48; 0x9dffc].
  idtac "MARK at pixCreate".
  rewrite ?(sx32_small (p_w v)) by (clear - HW0 HW2; lia). rewrite ?(sx32_small (p_h v)) by (clear - HH0 HH2; lia).
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => agf_side PFS NFA LOR Hx).
  idtac "MARK at_call pixCreate".
  assert (WR : 0 < p_w v <= 20000) by (clear - HW0 HW2; lia). assert (HR : 0 < p_h v <= 20000) by (clear - HH0 HH2; lia).
  assert (WQ1 : 1 <= (p_w v * 2 + 31) / 32) by (clear - WR; Z.div_mod_to_equations; lia).
  assert (WQ2 : (p_w v * 2 + 31) / 32 <= p_wpl v) by (rewrite HWPL, D8; apply Z.div_le_mono; clear - WR; lia).
  assert (WQ3 : (p_w v * 2 + 31) / 32 * p_h v <= p_wpl v * p_h v) by (apply Z.mul_le_mono_nonneg_r; clear - HR WQ2; lia).
  assert (HAO : hdr_args_ok (p_w v) (p_h v) 2) by (unfold hdr_args_ok; split; [cbn [In]; tauto|]; split; [exact WR|]; split; [exact HR|]; clear - WQ1 WQ3 HR HRS1; nia).
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
  assert (EWD : p_wpl v1 = (p_w v * 2 + 31) / 32) by (destruct HOKD as (_ & _ & _ & Q4 & _); rewrite VW, VD in Q4; exact Q4).
  assert (ERS : rs = 4 * (p_wpl v1 * p_h v)) by (unfold rs, rsize; rewrite VH; reflexivity).
  assert (RSD : 0 < 4 * (p_wpl v1 * p_h v) <= 67108864) by (destruct HOKD as (_ & _ & _ & _ & Q5); rewrite VH in Q5; exact Q5).
  hide POD. hide SUBP. hide SUBD. hide HOKD.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK before walk to PCR".
  walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCopyResolution; 0x9e45c].
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
  walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCopyInputFormat; 0x9e45c].
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
  walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixRemoveColormap; 0x9e45c].
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
    assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
      by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
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
  try forget_junk FR; try forget_junk FRM; try forget_junk FSH.
  destruct RMC as [(CM0 & EPT & PRC2)|(CMN & POSp & POT & WT & HT & DT & DATAT & CMT)].
  - (* [comment removed for export] *)
  (* [comment removed for export] *)
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
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9e494].
    idtac "MARK arm A at calloc 1".
    assert (WPLO : 0 < p_wpl v) by (rewrite EWS; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    assert (WPHI : p_wpl v <= 5001) by (rewrite EWS; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    rewrite !(sx32_small (p_wpl v)) by (clear - WPLO WPHI; lia).
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 1".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc1 : In (0x9e0c4 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT Σp _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
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
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9e494].
    idtac "MARK arm A at calloc 2".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 2".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc2 : In (0x9e0d8 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
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
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9e494].
    idtac "MARK arm A at calloc 3".
  (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 3".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc3 : In (0x9e100 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 256) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRc3]
           | |- _ => first [ unfold CALLOC_MAX; clear; lia
                           | rewrite LVB2; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                           | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
           end. }
    idtac "MARK calloc 3 applied".
    clear UCC.
    after_call RT AF.
    change (256 * 4)%Z with 1024%Z in *.
    fold_pres usp.
    idtac "MARK after calloc 3".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σt1; rename A into ARTT1 end.
    lazymatch goal with H : rt_live RT Σt1 = (?p, _) :: _ |- _ => rename H into LVT1N; rename p into tv end.
    lazymatch goal with H : rw_cells asegs _ tv [CB _ _] |- _ => rename H into T1Z end.
    assert (LVT1 : rt_live RT Σt1 = (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVT1N, LVB2; reflexivity).
    assert (FRSt1 : rt_frames RT Σt1 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σt1 = _ |- _ => rewrite E end; assumption).
    assert (SP0t1 : rt_sp0 RT Σt1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRt1 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σt1) by (repeat match goal with E : rt_credit RT Σt1 = _ |- _ => rewrite E end; assumption).
    lazymatch goal with H : 0 < tv |- _ => rename H into T10 end.
    lazymatch goal with H : tv mod 16 = 0 |- _ => rename H into T116 end.
    chunk_facts RT AF GP tv 1024. fframe_chunk RT AF fr 2%nat 256 tv 1024.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9e15c].
    idtac "MARK arm A at calloc 4".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 4".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc4 : In (0x9e110 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 256) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRc4]
           | |- _ => first [ unfold CALLOC_MAX; clear; lia
                           | rewrite LVT1; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                           | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
           end. }
    idtac "MARK calloc 4 applied".
    clear UCC.
    after_call RT AF.
    change (256 * 4)%Z with 1024%Z in *.
    fold_pres usp.
    idtac "MARK after calloc 4".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σt2; rename A into ARTT2 end.
    lazymatch goal with H : rt_live RT Σt2 = (?p, _) :: _ |- _ => rename H into LVT2N; rename p into t38 end.
    lazymatch goal with H : rw_cells asegs _ t38 [CB _ _] |- _ => rename H into T2Z end.
    assert (LVT2 : rt_live RT Σt2 = (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVT2N, LVT1; reflexivity).
    assert (FRSt2 : rt_frames RT Σt2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σt2 = _ |- _ => rewrite E end; assumption).
    assert (SP0t2 : rt_sp0 RT Σt2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRt2 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σt2) by (repeat match goal with E : rt_credit RT Σt2 = _ |- _ => rewrite E end; assumption).
    lazymatch goal with H : 0 < t38 |- _ => rename H into T20 end.
    lazymatch goal with H : t38 mod 16 = 0 |- _ => rename H into T216 end.
    chunk_facts RT AF GP t38 1024. fframe_chunk RT AF fr 2%nat 256 t38 1024.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9e15c].
    idtac "MARK arm A at calloc 5".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 5".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc5 : In (0x9e120 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 256) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRc5]
           | |- _ => first [ unfold CALLOC_MAX; clear; lia
                           | rewrite LVT2; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                           | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
           end. }
    idtac "MARK calloc 5 applied".
    clear UCC.
    after_call RT AF.
    change (256 * 4)%Z with 1024%Z in *.
    fold_pres usp.
    idtac "MARK after calloc 5".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σt3; rename A into ARTT3 end.
    lazymatch goal with H : rt_live RT Σt3 = (?p, _) :: _ |- _ => rename H into LVT3N; rename p into t14 end.
    lazymatch goal with H : rw_cells asegs _ t14 [CB _ _] |- _ => rename H into T3Z end.
    assert (LVT3 : rt_live RT Σt3 = (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVT3N, LVT2; reflexivity).
    assert (FRSt3 : rt_frames RT Σt3 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σt3 = _ |- _ => rewrite E end; assumption).
    assert (SP0t3 : rt_sp0 RT Σt3 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRt3 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σt3) by (repeat match goal with E : rt_credit RT Σt3 = _ |- _ => rewrite E end; assumption).
    lazymatch goal with H : 0 < t14 |- _ => rename H into T30 end.
    lazymatch goal with H : t14 mod 16 = 0 |- _ => rename H into T316 end.
    chunk_facts RT AF GP t14 1024. fframe_chunk RT AF fr 2%nat 256 t14 1024.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9e124; e_calloc].
    idtac "MARK arm A tables stored".
    try forget_junk FR; try forget_junk FRM; try forget_junk FSH; try forget_junk FRMb.
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx => agf_side PFS NFA LOR Hx) end.
    assert (NEB1 : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> bufs1)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σb1 _ [] bufs1 (p_wpl v * 4) _ e ARTB1 LVB1); [cbn [app]; exact He| clear - WPLO; lia| exact Hn]).
    assert (NEB2 : forall e, In e ((bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> bufs2)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σb2 _ [] bufs2 (p_wpl v * 4) _ e ARTB2 LVB2); [cbn [app]; exact He| clear - WPLO; lia| exact Hn]).
    assert (NET1 : forall e, In e ((bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> tv)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σt1 _ [] tv 1024 _ e ARTT1 LVT1); [cbn [app]; exact He| clear; lia| exact Hn]).
    assert (NET2 : forall e, In e ((tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> t38)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σt2 _ [] t38 1024 _ e ARTT2 LVT2); [cbn [app]; exact He| clear; lia| exact Hn]).
    assert (NET3 : forall e, In e ((t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> t14)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σt3 _ [] t14 1024 _ e ARTT3 LVT3); [cbn [app]; exact He| clear; lia| exact Hn]).
    assert (SUBB1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σb1) /\ fst e <> bufs1)
      by (intros e He; split; [rewrite LVB1; do 3 right; exact He| apply NEB1; [do 2 right; exact He| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBB2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σb2) /\ fst e <> bufs2)
      by (intros e He; split; [rewrite LVB2; do 4 right; exact He| apply NEB2; [do 3 right; exact He| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBT1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt1) /\ fst e <> tv)
      by (intros e He; split; [rewrite LVT1; do 5 right; exact He| apply NET1; [do 4 right; exact He| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBT2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt2) /\ fst e <> t38)
      by (intros e He; split; [rewrite LVT2; do 6 right; exact He| apply NET2; [do 5 right; exact He| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBT3 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt3) /\ fst e <> t14)
      by (intros e He; split; [rewrite LVT3; do 7 right; exact He| apply NET3; [do 6 right; exact He| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (NCB1 : forall a, PF a -> a < bufs1 \/ bufs1 + p_wpl v * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σb1 _ bufs1 (p_wpl v * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTB1 ltac:(rewrite LVB1; left; reflexivity) SUBB1);
          [ rewrite FRSb1; intros e He; right; exact He | rewrite SP0b1; ul | exact (proj1 Ha) ]).
    assert (NCB2 : forall a, PF a -> a < bufs2 \/ bufs2 + p_wpl v * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σb2 _ bufs2 (p_wpl v * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTB2 ltac:(rewrite LVB2; left; reflexivity) SUBB2);
          [ rewrite FRSb2; intros e He; right; exact He | rewrite SP0b2; ul | exact (proj1 Ha) ]).
    assert (NCT1 : forall a, PF a -> a < tv \/ tv + 1024 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σt1 _ tv 1024 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTT1 ltac:(rewrite LVT1; left; reflexivity) SUBT1);
          [ rewrite FRSt1; intros e He; right; exact He | rewrite SP0t1; ul | exact (proj1 Ha) ]).
    assert (NCT2 : forall a, PF a -> a < t38 \/ t38 + 1024 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σt2 _ t38 1024 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTT2 ltac:(rewrite LVT2; left; reflexivity) SUBT2);
          [ rewrite FRSt2; intros e He; right; exact He | rewrite SP0t2; ul | exact (proj1 Ha) ]).
    assert (NCT3 : forall a, PF a -> a < t14 \/ t14 + 1024 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σt3 _ t14 1024 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTT3 ltac:(rewrite LVT3; left; reflexivity) SUBT3);
          [ rewrite FRSt3; intros e He; right; exact He | rewrite SP0t3; ul | exact (proj1 Ha) ]).
    (* [comment removed for export] *)
    assert (N_b1b2 : bufs1 <> bufs2) by (exact (NEB2 (bufs1, p_wpl v * 4) ltac:(left; reflexivity) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_b1tv : bufs1 <> tv) by (exact (NET1 (bufs1, p_wpl v * 4) ltac:(right; left; reflexivity) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_b2tv : bufs2 <> tv) by (exact (NET1 (bufs2, p_wpl v * 4) ltac:(left; reflexivity) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_b1t38 : bufs1 <> t38) by (exact (NET2 (bufs1, p_wpl v * 4) ltac:(do 2 right; left; reflexivity) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_b2t38 : bufs2 <> t38) by (exact (NET2 (bufs2, p_wpl v * 4) ltac:(right; left; reflexivity) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_tvt38 : tv <> t38) by (exact (NET2 (tv, 1024) ltac:(left; reflexivity) ltac:(cbn [snd]; clear; lia))).
    assert (N_b1t14 : bufs1 <> t14) by (exact (NET3 (bufs1, p_wpl v * 4) ltac:(do 3 right; left; reflexivity) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_b2t14 : bufs2 <> t14) by (exact (NET3 (bufs2, p_wpl v * 4) ltac:(do 2 right; left; reflexivity) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_tvt14 : tv <> t14) by (exact (NET3 (tv, 1024) ltac:(right; left; reflexivity) ltac:(cbn [snd]; clear; lia))).
    assert (N_t38t14 : t38 <> t14) by (exact (NET3 (t38, 1024) ltac:(left; reflexivity) ltac:(cbn [snd]; clear; lia))).
    assert (N_pxb1 : pix <> bufs1) by (exact (NEB1 (pix, 64) ltac:(do 2 right; exact PIN) ltac:(cbn [snd]; clear; lia))).
    assert (N_pxb2 : pix <> bufs2) by (exact (NEB2 (pix, 64) ltac:(do 3 right; exact PIN) ltac:(cbn [snd]; clear; lia))).
    assert (N_pxtv : pix <> tv) by (exact (NET1 (pix, 64) ltac:(do 4 right; exact PIN) ltac:(cbn [snd]; clear; lia))).
    assert (N_pxt38 : pix <> t38) by (exact (NET2 (pix, 64) ltac:(do 5 right; exact PIN) ltac:(cbn [snd]; clear; lia))).
    assert (N_pxt14 : pix <> t14) by (exact (NET3 (pix, 64) ltac:(do 6 right; exact PIN) ltac:(cbn [snd]; clear; lia))).
    assert (N_pdb1 : pixd <> bufs1) by (exact (NEB1 (pixd, 64) ltac:(right; left; reflexivity) ltac:(cbn [snd]; clear; lia))).
    assert (N_pdb2 : pixd <> bufs2) by (exact (NEB2 (pixd, 64) ltac:(do 2 right; left; reflexivity) ltac:(cbn [snd]; clear; lia))).
    assert (N_pdtv : pixd <> tv) by (exact (NET1 (pixd, 64) ltac:(do 3 right; left; reflexivity) ltac:(cbn [snd]; clear; lia))).
    assert (N_pdt38 : pixd <> t38) by (exact (NET2 (pixd, 64) ltac:(do 4 right; left; reflexivity) ltac:(cbn [snd]; clear; lia))).
    assert (N_pdt14 : pixd <> t14) by (exact (NET3 (pixd, 64) ltac:(do 5 right; left; reflexivity) ltac:(cbn [snd]; clear; lia))).
    assert (N_dab1 : dat <> bufs1) by (exact (NEB1 (dat, rs) ltac:(left; reflexivity) DDN)).
    assert (N_dab2 : dat <> bufs2) by (exact (NEB2 (dat, rs) ltac:(right; left; reflexivity) DDN)).
    assert (N_datv : dat <> tv) by (exact (NET1 (dat, rs) ltac:(do 2 right; left; reflexivity) DDN)).
    assert (N_dat38 : dat <> t38) by (exact (NET2 (dat, rs) ltac:(do 3 right; left; reflexivity) DDN)).
    assert (N_dat14 : dat <> t14) by (exact (NET3 (dat, rs) ltac:(do 4 right; left; reflexivity) DDN)).
    assert (N_sdb1 : p_data v <> bufs1) by (exact (NEB1 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(do 2 right; exact DIN) DSZ)).
    assert (N_sdb2 : p_data v <> bufs2) by (exact (NEB2 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(do 3 right; exact DIN) DSZ)).
    assert (N_sdtv : p_data v <> tv) by (exact (NET1 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(do 4 right; exact DIN) DSZ)).
    assert (N_sdt38 : p_data v <> t38) by (exact (NET2 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(do 5 right; exact DIN) DSZ)).
    assert (N_sdt14 : p_data v <> t14) by (exact (NET3 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(do 6 right; exact DIN) DSZ)).
    idtac "MARK diseqs".
    lazymatch goal with A : ART RT Σt3 ?mm |- _ =>
      pose proof (live_apart2 RT AF Σt3 mm (pix) (64) (bufs1) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pxb1 (f_equal fst E)))) as A_pxb1;
      pose proof (live_apart2 RT AF Σt3 mm (pix) (64) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pxb2 (f_equal fst E)))) as A_pxb2;
      pose proof (live_apart2 RT AF Σt3 mm (pix) (64) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pxtv (f_equal fst E)))) as A_pxtv;
      pose proof (live_apart2 RT AF Σt3 mm (pix) (64) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pxt38 (f_equal fst E)))) as A_pxt38;
      pose proof (live_apart2 RT AF Σt3 mm (pix) (64) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pxt14 (f_equal fst E)))) as A_pxt14;
      pose proof (live_apart2 RT AF Σt3 mm (pixd) (64) (bufs1) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pdb1 (f_equal fst E)))) as A_pdb1;
      pose proof (live_apart2 RT AF Σt3 mm (pixd) (64) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pdb2 (f_equal fst E)))) as A_pdb2;
      pose proof (live_apart2 RT AF Σt3 mm (pixd) (64) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pdtv (f_equal fst E)))) as A_pdtv;
      pose proof (live_apart2 RT AF Σt3 mm (pixd) (64) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pdt38 (f_equal fst E)))) as A_pdt38;
      pose proof (live_apart2 RT AF Σt3 mm (pixd) (64) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pdt14 (f_equal fst E)))) as A_pdt14;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (bufs1) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dab1 (f_equal fst E)))) as A_dab1;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dab2 (f_equal fst E)))) as A_dab2;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_datv (f_equal fst E)))) as A_datv;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dat38 (f_equal fst E)))) as A_dat38;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dat14 (f_equal fst E)))) as A_dat14;
      pose proof (live_apart2 RT AF Σt3 mm (p_data v) (4 * (p_wpl v * p_h v)) (bufs1) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_sdb1 (f_equal fst E)))) as A_sdb1;
      pose proof (live_apart2 RT AF Σt3 mm (p_data v) (4 * (p_wpl v * p_h v)) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_sdb2 (f_equal fst E)))) as A_sdb2;
      pose proof (live_apart2 RT AF Σt3 mm (p_data v) (4 * (p_wpl v * p_h v)) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_sdtv (f_equal fst E)))) as A_sdtv;
      pose proof (live_apart2 RT AF Σt3 mm (p_data v) (4 * (p_wpl v * p_h v)) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_sdt38 (f_equal fst E)))) as A_sdt38;
      pose proof (live_apart2 RT AF Σt3 mm (p_data v) (4 * (p_wpl v * p_h v)) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_sdt14 (f_equal fst E)))) as A_sdt14;
      pose proof (live_apart2 RT AF Σt3 mm (bufs1) (p_wpl v * 4) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b1b2 (f_equal fst E)))) as A_b1b2;
      pose proof (live_apart2 RT AF Σt3 mm (bufs1) (p_wpl v * 4) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b1tv (f_equal fst E)))) as A_b1tv;
      pose proof (live_apart2 RT AF Σt3 mm (bufs1) (p_wpl v * 4) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b1t38 (f_equal fst E)))) as A_b1t38;
      pose proof (live_apart2 RT AF Σt3 mm (bufs1) (p_wpl v * 4) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b1t14 (f_equal fst E)))) as A_b1t14;
      pose proof (live_apart2 RT AF Σt3 mm (bufs2) (p_wpl v * 4) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b2tv (f_equal fst E)))) as A_b2tv;
      pose proof (live_apart2 RT AF Σt3 mm (bufs2) (p_wpl v * 4) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b2t38 (f_equal fst E)))) as A_b2t38;
      pose proof (live_apart2 RT AF Σt3 mm (bufs2) (p_wpl v * 4) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b2t14 (f_equal fst E)))) as A_b2t14;
      pose proof (live_apart2 RT AF Σt3 mm (tv) (1024) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_tvt38 (f_equal fst E)))) as A_tvt38;
      pose proof (live_apart2 RT AF Σt3 mm (tv) (1024) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_tvt14 (f_equal fst E)))) as A_tvt14;
      pose proof (live_apart2 RT AF Σt3 mm (t38) (1024) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_t38t14 (f_equal fst E)))) as A_t38t14 end.
    park A_pxb1. park A_pxb2. park A_pxtv. park A_pxt38. park A_pxt14. park A_pdb1. park A_pdb2. park A_pdtv. park A_pdt38. park A_pdt14. park A_dab1. park A_dab2. park A_datv. park A_dat38. park A_dat14. park A_sdb1. park A_sdb2. park A_sdtv. park A_sdt38. park A_sdt14. park A_b1b2. park A_b1tv. park A_b1t38. park A_b1t14. park A_b2tv. park A_b2t38. park A_b2t14. park A_tvt38. park A_tvt14. park A_t38t14.
    idtac "MARK apartness".
    assert (GEO : dt2_geom tv t38 t14 (usp + -304 + 152)).
    { unfold dt2_geom, SEGTOP_A. unfold parked in CKS5, CKH5, CKS6, CKH6, CKS7, CKH7, A_tvt38, A_tvt14, A_t38t14.
      clear - T10 T116 T20 T216 T30 T316 CKR5 CKR6 CKR7 CKS5 CKS6 CKS7 CKH5 CKH6 CKH7 SP0R1 A_tvt38 A_tvt14 A_t38t14 LOW LOR USP0 SPA SPT AL STa.
      repeat lazymatch goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia]. }
    park_disj.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32); (tv, tv + 1024); (t38, t38 + 1024); (t14, t14 + 1024)] [0x9e15c; e_calloc].
    idtac "MARK arm A at table loop".
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof T1Z as U1; apply u8arr_of_rw_cells in U1; destruct (u8arr_u32arr mm tv _ 256 U1 ltac:(rewrite repeat_length; clear; lia)) as (ws1 & UA1 & UAL1); clear U1;
      pose proof T2Z as U2; apply u8arr_of_rw_cells in U2; destruct (u8arr_u32arr mm t38 _ 256 U2 ltac:(rewrite repeat_length; clear; lia)) as (ws2 & UA2 & UAL2); clear U2;
      pose proof T3Z as U3; apply u8arr_of_rw_cells in U3; destruct (u8arr_u32arr mm t14 _ 256 U3 ltac:(rewrite repeat_length; clear; lia)) as (ws3 & UA3 & UAL3); clear U3 end.
    pose proof FR as CA. split_at CA 14%nat CA2. split_at CA2 1%nat CA3. clear CA CA3.
    lazymatch type of CA2 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 152) in CA2 by (clear; lia) end.
    idtac "MARK table premises".
    eapply evt_cut.
    { lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        epose proof (dt2_tables 256%nat 0 _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm mm (usp + -304) tv t38 t14 ws1 ws2 ws3
                       ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia) GEO (munch_refl [(tv, tv + 1024); (t38, t38 + 1024); (t14, t14 + 1024)] mm) (wmono_refl asegs mm) MIx
                       UA1 UAL1 ltac:(assumption) UA2 UAL2 ltac:(assumption) UA3 UAL3 ltac:(assumption) CA2) as ZR end.
      unfold SHB in ZR. exact ZR. }
    idtac "MARK tables applied".
    intros ms' PO. unfold dt2_exit in PO.
    destruct PO as (ra' & a0' & a1' & a2' & a5' & a6' & s3' & s6' & s7' & t6' & mt & ws1' & ws2' & ws3' & -> & MUt & WMt & MIt & UA1' & UAL1' & ACC1' & UA2' & UAL2' & ACC2' & UA3' & UAL3' & ACC3' & CAt).
    idtac "MARK tables post".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    hide FRM. hide FSH. hide PXD. hide PXS. clear B1Z B2Z T1Z T2Z T3Z UA1 UA2 UA3 UAL1 UAL2 UAL3 CA2.
    loop_art RT AF Σt3 mt lo MUt ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; right; right; left; exists tv, 1024; split; [solve [find_in]| clear - Hzz; lia]| split; [intros zz Hzz; right; right; left; exists t38, 1024; split; [solve [find_in]| clear - Hzz; lia]| split; [intros zz Hzz; right; right; left; exists t14, 1024; split; [solve [find_in]| clear - Hzz; lia]| exact I]]]]]]).
    idtac "MARK tables loop_art".
    lazymatch type of MUt with munch _ ?ma ?mb =>
      loop_transport ma mb MUt ltac:(fun Hx => clear - Hx CKR5 CKR6 CKR7 CKS5 CKS6 CKS7 LOW LOR STa SP0R0; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
    idtac "MARK tables loop_transport".
    carry_mu MUt FRM ltac:(fun Hx => unfold parked in FCD5, FCD6, FCD7; clear - Hx FCD5 FCD6 FCD7; repeat split; try exact I; lia).
    carry_mu MUt FSH ltac:(fun Hx => unfold parked in FCS5, FCS6, FCS7; clear - Hx FCS5 FCS6 FCS7 FR64; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    carry_mu MUt PXD ltac:(fun Hx => unfold parked in A_pdtv, A_pdt38, A_pdt14; clear - Hx A_pdtv A_pdt38 A_pdt14; repeat split; try exact I; lia).
    carry_mu MUt PXS ltac:(fun Hx => unfold parked in A_pxtv, A_pxt38, A_pxt14; clear - Hx A_pxtv A_pxt38 A_pxt14; repeat split; try exact I; lia).
    idtac "MARK tables carried".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; right; right; left; exists tv, 1024; split; [solve [find_in]| clear - Hzz; lia]| split; [intros zz Hzz; right; right; left; exists t38, 1024; split; [solve [find_in]| clear - Hzz; lia]| split; [intros zz Hzz; right; right; left; exists t14, 1024; split; [solve [find_in]| clear - Hzz; lia]| exact I]]]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx =>
      pose proof (NCT1 _ Hx) as Y1; pose proof (NCT2 _ Hx) as Y2; pose proof (NCT3 _ Hx) as Y3; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [Hx1 Hx2];
      cbn [outside]; unfold shad, SHB in *; clear - P1 N1 N2 Hx2 LOR Y1 Y2 Y3; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK after tables".
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_asan_memcpy; 0x9e15c].
    idtac "MARK arm A at memcpy 1".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite ?(sx32_small (p_w v)) by (clear - HW0 HW2; lia). rewrite ?(sx32_small (p_h v)) by (clear - HH0 HH2; lia).
    rewrite ?(bv_swrap_small 32 (p_wpl v * 4)) by (change (bv_half_modulus 32) with (2^31); clear - WPLO WPHI; lia).
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call memcpy 1".
    assert (NLE : p_wpl v * 4 <= 4 * (p_wpl v * p_h v)) by (clear - WPLO HH0; nia).
    lazymatch goal with A : ART RT Σt3 ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (af_acc_live RT AF Σt3 mm (p_data v) (4 * (p_wpl v * p_h v)) A ltac:(solve [find_in])) as (WRS & ACCS);
      pose proof (af_acc_live RT AF Σt3 mm bufs2 (p_wpl v * 4) A ltac:(solve [find_in])) as (WR2 & ACCB) end.
    apply wr_at_rw_CB in WRS; [| clear - HRS0; lia]. destruct WRS as (sbs & SBC).
    pose proof SBC as [[[SBL _] _] _]. cbn in SBL.
    apply u8arr_of_rw_cells in SBC. destruct SBC as [SB _].
    rewrite <- (firstn_skipn (Z.to_nat (p_wpl v * 4)) sbs) in SB. apply bytes_at_app in SB. destruct SB as [SB1 _].
    assert (SBL1 : Z.of_nat (length (firstn (Z.to_nat (p_wpl v * 4)) sbs)) = p_wpl v * 4) by (rewrite firstn_length_le; [clear - WPLO; lia| rewrite SBL; clear - WPLO NLE; lia]).
    assert (Q7a : 0 <= bufs2 <= 2^47) by (clear - CKR4 SP0R1 B20 WPLO; lia).
    assert (Q7b : 0 <= p_data v <= 2^47) by (clear - CKR0 SP0R1 D0 HRS0; lia).
    assert (Q3 : bufs2 + p_wpl v * 4 <= p_data v \/ p_data v + p_wpl v * 4 <= bufs2) by (unfold parked in A_sdb2; clear - A_sdb2 NLE; lia).
    assert (Q4 : p_data v + p_wpl v * 4 <= lo) by (clear - CKR0 LOW NLE; lia).
    eapply cps_seq.
    { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
      eapply MC0 with (lo := lo) (d := bufs2) (s := p_data v) (bs := firstn (Z.to_nat (p_wpl v * 4)) sbs); rewrite ?SBL1.
      all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; clear - WPLO; lia
         | |- bytes_at _ _ _ _ => exact SB1
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ => unfold checked_src; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
             split; [intros _; split; [eapply acc_sub; [exact ACCS| clear; lia | clear - NLE; lia] | left; exists (p_data v), (4 * (p_wpl v * p_h v)); split; [solve [find_in]| clear - NLE WPLO; lia]] | left; exact Q4]
         | |- checked_dst _ _ _ _ _ _ => unfold checked_dst; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
             split; [intros _; split; [exact ACCB| left; exists bufs2, (p_wpl v * 4); split; [solve [find_in]| clear; lia]]|];
             split; [intros i Hi; right; right; left; exists bufs2, (p_wpl v * 4); split; [solve [find_in]| clear - Hi; lia]| exact WR2]
         | |- call_ok _ _ _ _ _ => call_ok_tac2 SPA
         | |- _ \/ _ => exact Q3
         | |- (_ <= _ <= _) => first [exact Q7a | exact Q7b]
         | |- (_ < _) => clear - WPLO WPHI; lia
         | |- ?g => idtac "LEFT:" g
         end. }
    idtac "MARK memcpy 1 applied".
    rewrite SBL1. clear SB1 SBL1 ACCS ACCB WR2.
    hide FRM. hide FSH. hide PXD. hide PXS.
    after_call RT AF.
    idtac "MARK after_call memcpy 1".
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => fr_side fr Hx);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => sh_side fr FR64 Hx);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in A_pdb2; clear - Hx A_pdb2; lia);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in A_pxb2; clear - Hx A_pxb2; lia) end.
    idtac "MARK carried memcpy 1".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; pose proof (NCB2 _ (conj Hx1 Hx2)) as Y; clear - Y; lia).
    repeat match goal with H : bytes_at asegs _ bufs2 _ |- _ => clear H end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK after memcpy 1".
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9e66c; e_asan_memcpy].
    idtac "MARK arm A at h test".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (WPLD1 : 0 < p_wpl v1) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    assert (WPLD2 : p_wpl v1 <= 1251) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    rewrite ?(bv_swrap_small 32 (p_h v + -1)) by (change (bv_half_modulus 32) with (2^31); clear - HH0 HH2; lia).
    rewrite ?(bv_swrap_small 32 (p_h v + -1)) in FR by (change (bv_half_modulus 32) with (2^31); clear - HH0 HH2; lia).
    rewrite ?(bv_swrap_small 32 (p_wpl v * 4)) in FR by (change (bv_half_modulus 32) with (2^31); clear - WPLO WPHI; lia).
    rewrite ?(sx32_small (p_wpl v1)) in FR by (clear - WPLD1 WPLD2; lia).
    replace (p_wpl v * 4) with (4 * p_wpl v) in FR by (clear; lia).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx => agf_side PFS NFA LOR Hx) end.
    lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      set (JC := d2_join RT Σt3 PMc gp sp (usp + -304) 304 lo fr (fr / 8 + 2147450880) (p_w v) (p_h v) (p_wpl v) (p_wpl v1) (p_data v) dat rs bufs1 bufs2 (p_wpl v * 4) tv t38 t14 40%nat
                 [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] mm); rename mm into mh end.
    idtac "MARK JC set".
    eapply cps_seq with (Q := JC).
    {
    walk_to AF MST [(usp - 368, usp)] [0x9e66c].
    lstep.
    destruct (Z.eq_dec (p_h v) 1) as [HONE|HTWO].
    + (* [comment removed for export] *)
      brT.
      awalk [0x9eae4; 0x9e6a8].
      rewrite ?(bv_swrap_small 32 (p_w v + -1)) by (change (bv_half_modulus 32) with (2^31); clear - HW0 HW2; lia).
      cps_stop.
      idtac "MARK h1 at join".
      apply cps_finish. intros c Hc. subst JC. unfold d2_join. eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-.
      pose proof FR as F1. split_at F1 6%nat F2. split_at F2 10%nat F3.
      lazymatch type of F2 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 56) in F2 by (clear; lia) end.
      lazymatch type of F3 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 160) in F3 by (clear; lia) end.
      forget_cells F1 0%nat 2%nat. forget_cells F3 0%nat 3%nat.
      do 24 eexists.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
      apply agree_refl.
    + (* [comment removed for export] *)
      brF.
      awalk [0x9e6a8].
      idtac "MARK h2 at rows".
      rewrite ?(bv_swrap_small 32 (p_w v + -1)) by (change (bv_half_modulus 32) with (2^31); clear - HW0 HW2; lia).
      rewrite ?(bv_swrap_small 32 (p_w v + -1)) in FR by (change (bv_half_modulus 32) with (2^31); clear - HW0 HW2; lia).
      replace (Z.land (p_w v + -1) 18446744073709551615) with (p_w v + -1) in FR
        by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); symmetry; apply Z.mod_small; clear - HW0 HW2; lia).
      replace (Z.land ((p_w v + -1) * 4294967296) 18446744073709551615) with ((p_w v + -1) * 4294967296) in FR
        by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); symmetry; apply Z.mod_small; clear - HW0 HW2; lia).
      replace ((p_w v + -1) * 4294967296 / 4294967296) with (p_w v + -1) in FR by (symmetry; apply Z.div_mul; clear; lia).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      assert (GEOM : d2r_geom (rt_sp0 RT Σt3) lo (usp + -304) dat rs (p_data v) (4 * (p_wpl v * p_h v)) bufs1 bufs2 (p_wpl v * 4) (p_wpl v) (p_wpl v1) (p_w v) (p_h v) tv t38 t14).
      { rewrite SP0t3. unfold d2r_geom, LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A.
        assert (QG1 : p_wpl v1 <= p_wpl v) by (rewrite EWD, EWS; apply Z.div_le_mono; clear - HW0; lia).
        assert (QG2 : p_w v <= 4 * p_wpl v) by (rewrite EWS; clear - HW0; Z.div_mod_to_equations; lia).
        assert (QG3 : p_w v <= 16 * p_wpl v1) by (rewrite EWD; clear - HW0; Z.div_mod_to_equations; lia).
        assert (QG4 : 0 < rs <= 4 * (p_wpl v * p_h v)) by (rewrite ERS; clear - QG1 WPLD1 HH0; nia).
        clear - QG1 QG2 QG3 QG4 WPLO WPHI WPLD1 WPLD2 HW0 HW2 HH0 HH2 HRS0 HRS1 NLE ERS DD0 DD16 CKR2 CKS2 CKH2 D0 D16 CKR0 CKS0 CKH0 B10 B116 CKR3 CKS3 CKH3 B20 B216 CKR4 CKS4 CKH4
                T10 T116 CKR5 CKS5 CKH5 T20 T216 CKR6 CKS6 CKH6 T30 T316 CKR7 CKS7 CKH7 DRD A_dab1 A_dab2 A_sdb1 A_sdb2 A_b1b2 A_datv A_b1tv A_b2tv A_dat38 A_b1t38 A_b2t38 A_dat14 A_b1t14 A_b2t14
                LOW LOR SPT SPA AL SPB SP0R0 SP0R1 SP0W STa USP0.
        repeat lazymatch goal with |- _ /\ _ => split end; por. }
      idtac "MARK GEOM".
      pose proof FR as F1. split_at F1 6%nat F2. split_at F2 13%nat F3.
      lazymatch type of F2 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 56) in F2 by (clear; lia) end.
      lazymatch type of F3 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 160) in F3 by (clear; lia) end.
      hide F1. hide F3. hide FRM. hide FSH. hide PXD. hide PXS. clear FR.
      eapply cps_seq.
      { eapply (d2_rows RT AF GP RC (Z.to_nat (p_h v - 1)) 0) with (lo := lo) (rd := rs) (rs := 4 * (p_wpl v * p_h v)) (n1 := p_wpl v * 4) (wpls := p_wpl v) (wpld := p_wpl v1)
               (w := p_w v) (h := p_h v) (datad := dat) (datas := p_data v) (t14 := t14) (ic := Z_to_bv 64 (fr + 48)).
        all: lazymatch goal with
          | |- Z.of_nat _ = _ => clear - HH0 HTWO; lia
          | |- 0 <= 0 => clear; lia
          | |- (1 <= _)%nat => clear - HH0 HTWO; lia
          | |- fdfs_only _ => exact FDO
          | |- mat_stable _ => exact MST
          | |- d2r_geom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact GEOM
          | |- In _ _ => solve [find_in]
          | |- ART _ _ _ => assumption
          | |- mem_inv _ _ => assumption
          | |- stk _ _ _ _ => assumption
          | |- LIBH _ => assumption
          | |- io_ssp _ => assumption
          | |- rw_cells _ _ _ _ => exact F2
          | |- ?g => idtac "LEFT:" g
          end. }
      idtac "MARK rows applied".
      clear F2 GEOM.
      unfold d2r_post. after_call RT AF.
      idtac "MARK rows opened".
      lazymatch goal with H : rw_cells asegs _ _ (d2r_frame _ _ _ _ _ _ _ _ _ _) |- _ => rename H into FBK; unfold d2r_frame in FBK end.
      lazymatch goal with H : agree_on (d2r_keep _ _ _ _ _ _ _ _) ?ma ?mb |- _ => rename H into AGR; rename ma into mh2 end.
      unfold d2r_keep in AGR.
      carry AGR F1 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR2 CKR3 CKR4 LOW LOR; repeat split; try exact I; lia).
      carry AGR F3 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR2 CKR3 CKR4 LOW LOR; repeat split; try exact I; lia).
      idtac "MARK rows carried".
      pose proof FBK as FBKn. norm_cells FBKn.   (* [comment removed for export] *)
      walk_to AF MST [(usp - 368, usp)] [0x9eae4].
      cps_stop. clear FBKn.
      idtac "MARK h2 at join".
      apply cps_finish. intros c Hc. subst JC. unfold d2_join. eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-.
      forget_cells F1 0%nat 2%nat. forget_cells FBK 0%nat 4%nat. forget_cells F3 0%nat 3%nat.
      do 24 eexists.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [exact F1|]. split; [exact FBK|]. split; [exact F3|].
      lazymatch goal with MUx : munch _ mh mh2 |- agree_on _ mh ?m3 =>
        apply (agree_trans _ mh mh2 m3);
        [ eapply agree_sub; [exact (agree_of_munch _ mh mh2 _ MUx (fun x Hx => Hx))|]; cbv beta; intros a9 [Ha91 Ha92]; cbn [outside] in Ha92; cbn [outside];
          destruct (aclient_split RT AF Σt3 _ (usp + -304) a9 ltac:(eassumption) Ha91) as [Q|Q]; (split; [| exact I]); unfold STACK_WIN in *; clear - Q Ha92 LOW LOR SP0t3; lia
        | eapply agree_sub; [exact AGR|]; cbv beta; intros a9 [Ha91 Ha92]; split; [exact Ha91| cbn [outside] in Ha92; cbn [outside]; clear - Ha92; repeat split; try exact I; lia] ] end.
    }
    idtac "MARK joined".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    subst JC. unfold d2_join. after_call RT AF.
    idtac "MARK J opened".
    lazymatch goal with A : ART RT Σt3 ?mq |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mq _))) _ => rename A into ARTJ; rename mq into mj end.
    lazymatch goal with H : rw_cells asegs mj (usp + -304) _ |- _ => rename H into F1 end.
    lazymatch goal with H : rw_cells asegs mj (usp + -304 + 56) _ |- _ => rename H into F2 end.
    lazymatch goal with H : rw_cells asegs mj (usp + -304 + 160) _ |- _ => rename H into F3 end.
    lazymatch goal with H : agree_on _ mh mj |- _ => rename H into AGJ end.
    clear FR.
    carry AGJ FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia])
      ltac:(fun Hx => repeat match goal with Hf : parked (fr + 256 <= ?b \/ _ <= fr) |- _ => unfold parked in Hf; revert Hf end; clear - Hx FRHI LOW LOR; intros; repeat split; try exact I; lia).
    carry AGJ FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia])
      ltac:(fun Hx => repeat match goal with Hf : parked (?b + _ <= fr / 8 + 2147450880 \/ (fr + 256) / 8 + 2147450880 <= ?b) |- _ => unfold parked in Hf; revert Hf end;
                      unfold shad, SHB in *; clear - Hx FR64 FRHI SP0R1 SP0W LOW LOR; intros; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    carry AGJ PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx])
      ltac:(fun Hx => unfold parked in DPD, A_pdb1, A_pdb2; clear - Hx DPD A_pdb1 A_pdb2 CKR1 LOW LOR; repeat split; try exact I; lia).
    carry AGJ PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx])
      ltac:(fun Hx => unfold parked in DSD, A_pxb1, A_pxb2; clear - Hx DSD A_pxb1 A_pxb2 CKR LOW LOR; repeat split; try exact I; lia).
    idtac "MARK J carried".
    assert (AGF2 : agree_on PF m mj).
    { apply (agree_trans PF m mh mj AGF). eapply agree_sub; [exact AGJ|]. cbv beta. intros a9 Ha9.
      pose proof (PFS _ Ha9) as P9. pose proof (NCD _ Ha9) as Y1. pose proof (NCB1 _ Ha9) as Y2. pose proof (NCB2 _ Ha9) as Y3.
      destruct Ha9 as [Ha91 Ha92]. split.
      - apply (aclient_mono _ _ usp _ _ _ _ Ha91); [intros e He; rewrite LVT3; do 7 right; exact He| rewrite FRSt3; intros e He; right; exact He| clear; lia].
      - cbn [outside]. clear - P9 Y1 Y2 Y3 ERS LOR. repeat split; try exact I; lia. }
    clear AGF AGJ. rename AGF2 into AGF.
    join_cells F1 F2. join_cells F1 F3. rename F1 into FR.
    repeat match goal with H : context [mh] |- _ => clear H end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK after join".
    try forget_junk FR; try forget_junk FRM; try forget_junk FSH; try forget_junk FRMb.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_asan_memcpy].
    idtac "MARK arm A at memcpy L".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call memcpy L".
    lazymatch goal with A : ART RT Σt3 ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (af_acc_live RT AF Σt3 mm bufs2 (p_wpl v * 4) A ltac:(solve [find_in])) as (WRS & ACCS);
      pose proof (af_acc_live RT AF Σt3 mm bufs1 (p_wpl v * 4) A ltac:(solve [find_in])) as (WRB & ACCB) end.
    apply wr_at_rw_CB in WRS; [| clear - WPLO; lia]. destruct WRS as (cbs & SBC).
    pose proof SBC as [[[SBL2 _] _] _]. cbn in SBL2.
    apply u8arr_of_rw_cells in SBC. destruct SBC as [SB2 _].
    assert (SBL1 : Z.of_nat (length cbs) = p_wpl v * 4) by (rewrite SBL2; clear - WPLO; lia).
    assert (Q8a : 0 <= bufs1 <= 2^47) by (clear - CKR3 SP0R1 B10 WPLO; lia).
    assert (Q8b : 0 <= bufs2 <= 2^47) by (clear - CKR4 SP0R1 B20 WPLO; lia).
    assert (Q6 : bufs1 + p_wpl v * 4 <= bufs2 \/ bufs2 + p_wpl v * 4 <= bufs1) by (unfold parked in A_b1b2; clear - A_b1b2; lia).
    assert (Q5 : bufs2 + p_wpl v * 4 <= lo) by (clear - CKR4 LOW; lia).
    eapply cps_seq.
    { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
      eapply MC0 with (lo := lo) (d := bufs1) (s := bufs2) (bs := cbs); rewrite ?SBL1.
      all: lazymatch goal with
           | |- fdfs_only _ => exact FDO
           | |- mat_stable _ => exact MST
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; clear - WPLO; lia
           | |- bytes_at _ _ _ _ => exact SB2
           | |- ART _ _ _ => assumption
           | |- mem_inv _ _ => assumption
           | |- checked_src _ _ _ _ _ _ _ =>
               unfold checked_src; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
               split; [intros _; split; [exact ACCS | left; exists bufs2, (p_wpl v * 4); split; [solve [find_in]| clear; lia]] | left; exact Q5]
           | |- checked_dst _ _ _ _ _ _ =>
               unfold checked_dst; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
               split; [intros _; split; [exact ACCB| left; exists bufs1, (p_wpl v * 4); split; [solve [find_in]| clear; lia]]|];
               split; [intros i0 Hi; right; right; left; exists bufs1, (p_wpl v * 4); split; [solve [find_in]| clear - Hi; lia]| exact WRB]
           | |- call_ok _ _ _ _ _ => call_ok_tac2 SPA
           | |- _ \/ _ => exact Q6
           | |- (_ <= _ <= _) => first [exact Q8a | exact Q8b]
           | |- (_ < _) => clear - WPLO WPHI; lia
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK memcpy L applied".
    rewrite SBL1. clear SB2 SBL1 SBL2 ACCS ACCB WRB.
    hide FRM. hide FSH. hide PXD. hide PXS.
    after_call RT AF.
    idtac "MARK after_call memcpy L".
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => fr_side fr Hx);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => sh_side fr FR64 Hx);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in A_pdb1; clear - Hx A_pdb1; lia);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in A_pxb1; clear - Hx A_pxb1; lia) end.
    idtac "MARK carried memcpy L".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; pose proof (NCB1 _ (conj Hx1 Hx2)) as Y; clear - Y; lia).
    lazymatch goal with H : bytes_at asegs ?mm bufs1 cbs |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename H into CB1 end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK after memcpy L".
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9eb14].
    idtac "MARK arm A at last line".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite ?(bv_swrap_small 32 ((p_h v - 1) * p_wpl v1)) by (change (bv_half_modulus 32) with (2^31); clear - HH0 HH2 WPLD1 WPLD2; nia).
    replace (Z.land ((p_h v - 1) * p_wpl v1) 18446744073709551615) with ((p_h v - 1) * p_wpl v1)
      by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); symmetry; apply Z.mod_small; clear - HH0 HH2 WPLD1 WPLD2; nia).
    assert (HM0 : 0 <= (p_h v - 1) * p_wpl v1 * 4) by (clear - HH0 WPLD1; nia).
    assert (HM1 : (p_h v - 1) * p_wpl v1 * 4 + 4 * p_wpl v1 = rs) by (rewrite ERS; clear; lia).
    set (lined := dat + (p_h v - 1) * p_wpl v1 * 4) in *.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx => agf_side PFS NFA LOR Hx) end.
    clear_acc. refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    (* [comment removed for export] *)
    assert (L1 : 0 < lined) by (unfold lined; clear - DD0 HM0; lia).
    assert (L2 : lined mod 4 = 0) by (unfold lined; clear - DD16 HM0; Z.div_mod_to_equations; lia).
    assert (L3 : lined + 4 * p_wpl v1 <= 2^47) by (unfold lined; clear - CKR2 SP0R1 HM0 HM1; lia).
    assert (L4 : lined + 4 * p_wpl v1 <= 0x7fff7000 \/ 0x10007fff8000 <= lined) by (unfold lined; unfold parked in CKH2; clear - CKH2 HM0 HM1; lia).
    assert (L5 : lined + 4 * p_wpl v1 <= 0x10000 \/ 6569984 <= lined) by (unfold lined; unfold parked in CKS2; clear - CKS2 HM0 HM1; lia).
    assert (L6 : bufs1 + p_wpl v * 4 <= lined \/ lined + 4 * p_wpl v1 <= bufs1) by (unfold lined; unfold parked in A_dab1; clear - A_dab1 HM0 HM1; lia).
    assert (L7 : bufs2 + p_wpl v * 4 <= lined \/ lined + 4 * p_wpl v1 <= bufs2) by (unfold lined; unfold parked in A_dab2; clear - A_dab2 HM0 HM1; lia).
    assert (L8 : tv + 1024 <= lined \/ lined + 4 * p_wpl v1 <= tv) by (unfold lined; unfold parked in A_datv; clear - A_datv HM0 HM1; lia).
    assert (L9 : t38 + 1024 <= lined \/ lined + 4 * p_wpl v1 <= t38) by (unfold lined; unfold parked in A_dat38; clear - A_dat38 HM0 HM1; lia).
    assert (L10 : t14 + 1024 <= lined \/ lined + 4 * p_wpl v1 <= t14) by (unfold lined; unfold parked in A_dat14; clear - A_dat14 HM0 HM1; lia).
    assert (L11 : p_w v <= p_wpl v * 4) by (rewrite EWS; clear - HW0; Z.div_mod_to_equations; lia).
    assert (L12 : p_w v <= 4 * (4 * p_wpl v1)) by (rewrite EWD; clear - HW0; Z.div_mod_to_equations; lia).
    assert (L13 : bufs2 + p_wpl v * 4 <= bufs1 \/ bufs1 + p_wpl v * 4 <= bufs2) by (unfold parked in A_b1b2; clear - A_b1b2; lia).
    assert (GEO1 : d2_geom lined (4 * p_wpl v1) bufs1 bufs2 (p_wpl v * 4) tv t38 t14 (p_w v)).
    { unfold d2_geom, SEGTOP_A.
      clear - L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 HW0 HW2 WPLO WPHI WPLD1 WPLD2 B10 B116 CKR3 CKS3 CKH3 B20 B216 CKR4 CKS4 CKH4
              T10 T116 CKR5 CKS5 CKH5 T20 T216 CKR6 CKS6 CKH6 T30 T316 CKR7 CKS7 CKH7 A_b1tv A_b2tv A_b1t38 A_b2t38 A_b1t14 A_b2t14 SP0R1.
      repeat lazymatch goal with |- _ /\ _ => split end; por. }
    idtac "MARK GEO1".
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT Σt3 ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (af_acc_live RT AF Σt3 mm bufs1 (p_wpl v * 4) A ltac:(solve [find_in])) as (WQB & AQB);
      pose proof (af_acc_live RT AF Σt3 mm dat rs A ltac:(solve [find_in])) as (WQD & AQD);
      pose proof (af_acc_live RT AF Σt3 mm tv 1024 A ltac:(solve [find_in])) as (WQT & AQT);
      pose proof (af_acc_live RT AF Σt3 mm t38 1024 A ltac:(solve [find_in])) as (WQ8 & AQ8) end.
    apply wr_at_rw_CB in WQB; [| clear - WPLO; lia]. destruct WQB as (lbs & QB). pose proof QB as [[[QBL _] _] _]. cbn in QBL. apply u8arr_of_rw_cells in QB.
    assert (QBL1 : Z.of_nat (length lbs) = p_wpl v * 4) by (rewrite QBL; clear - WPLO; lia). clear QBL.
    apply (wr_at_sub _ _ _ lined (4 * p_wpl v1)) in WQD; [| unfold lined; clear - HM0; lia | unfold lined; clear - HM0 HM1; lia | clear - WPLD1; lia].
    apply wr_at_rw_CB in WQD; [| clear - WPLD1; lia]. destruct WQD as (ljunk & QD). pose proof QD as [[[QDL _] _] _]. cbn in QDL. apply u8arr_of_rw_cells in QD.
    destruct (u8arr_u32arr _ lined ljunk (p_wpl v1) QD ltac:(rewrite QDL; clear - WPLD1; lia)) as (lwl & UQL & UQLL). clear QD QDL.
    assert (AQL : acc asegs _ lined (4 * p_wpl v1)) by (eapply acc_sub; [exact AQD| unfold lined; clear - HM0; lia | unfold lined; clear - HM0 HM1; lia]).
    apply wr_at_rw_CB in WQT; [| clear; lia]. destruct WQT as (tjunk & QT). pose proof QT as [[[QTL _] _] _]. cbn in QTL. apply u8arr_of_rw_cells in QT.
    destruct (u8arr_u32arr _ tv tjunk 256 QT ltac:(rewrite QTL; clear; lia)) as (ltw & UQT & UQTL). clear QT QTL.
    apply wr_at_rw_CB in WQ8; [| clear; lia]. destruct WQ8 as (t8junk & Q8). pose proof Q8 as [[[Q8L _] _] _]. cbn in Q8L. apply u8arr_of_rw_cells in Q8.
    destruct (u8arr_u32arr _ t38 t8junk 256 Q8 ltac:(rewrite Q8L; clear; lia)) as (lt8 & UQ8 & UQ8L). clear Q8 Q8L.
    pose proof FR as CBF. split_at CBF 12%nat CBF2. split_at CBF2 1%nat CBF3. clear CBF CBF3.
    lazymatch type of CBF2 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 136) in CBF2 by (clear; lia) end.
    idtac "MARK last-line premises".
    walk_to AF MST [(lined, lined + 4 * p_wpl v1); (bufs1, bufs1 + p_wpl v * 4)] [0x9eb14].
    eapply evt_cut.
    { lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        epose proof (d2l1_line _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -304) lined (4 * p_wpl v1) bufs1 bufs2 (p_wpl v * 4) tv t38 t14 (p_w v) lbs lwl ltw lt8
                       GEO1 MIx QB QBL1 ltac:(assumption) UQL ltac:(rewrite UQLL; clear; lia) AQL UQT UQTL ltac:(assumption) UQ8 UQ8L ltac:(assumption) CBF2
                       ltac:(clear - LOR STa; lia) ltac:(clear - SPT; lia) ltac:(unfold lined; clear - CKR2 LOW LOR HM0 HM1; lia) ltac:(clear - CKR3 LOW LOR; lia)) as ZR end.
      unfold SHB in ZR. exact ZR. }
    idtac "MARK last line applied".
    clear QB UQL AQL UQT UQ8 CBF2.
    intros ms' PO. unfold d2l1_end in PO.
    destruct PO as (qt0 & qt1 & qt2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & qt3 & qt4 & qt5 & mE & lbs2 & lwl2 & -> & MUl & WMl & MIl & UB' & UBL' & ACCB' & UL' & ULL' & ACCL' & UT' & ACCT' & U38' & ACC38').
    clear UB' UBL' UL' ULL' UT' U38'.
    idtac "MARK last line post".
    hide FRM. hide FSH. hide PXD. hide PXS.
    loop_art RT AF Σt3 mE lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [solve [find_in]| unfold lined in Hzz; clear - Hzz HM0 HM1; lia]| split; [intros zz Hzz; right; right; left; exists bufs1, (p_wpl v * 4); split; [solve [find_in]| clear - Hzz; lia]| exact I]]).
    lazymatch type of MUl with munch _ ?ma ?mb =>
      loop_transport ma mb MUl ltac:(fun Hx => clear - Hx CKR2 CKR3 CKS2 CKS3 LOW LOR STa SP0R0 HM0 HM1 WPLD1 WPLO; unfold parked in *; unfold lined; first [lia | Z.div_mod_to_equations; lia]) end.
    idtac "MARK last line transported".
    carry_mu MUl FRM ltac:(fun Hx => repeat match goal with Hf : parked (fr + 256 <= ?b \/ _ <= fr) |- _ => unfold parked in Hf; revert Hf end; unfold lined; clear - Hx HM0 HM1; intros; repeat split; try exact I; lia).
    carry_mu MUl FSH ltac:(fun Hx => repeat match goal with Hf : parked (?b + _ <= fr / 8 + 2147450880 \/ (fr + 256) / 8 + 2147450880 <= ?b) |- _ => unfold parked in Hf; revert Hf end;
                             unfold shad, SHB in *; unfold lined; clear - Hx FR64 HM0 HM1; intros; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    carry_mu MUl PXD ltac:(fun Hx => unfold parked in DPD, A_pdb1; unfold lined; clear - Hx DPD A_pdb1 HM0 HM1; repeat split; try exact I; lia).
    carry_mu MUl PXS ltac:(fun Hx => unfold parked in DSD, A_pxb1; unfold lined; clear - Hx DSD A_pxb1 HM0 HM1; repeat split; try exact I; lia).
    idtac "MARK last line carried".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [solve [find_in]| unfold lined in Hzz; clear - Hzz HM0 HM1; lia]| split; [intros zz Hzz; right; right; left; exists bufs1, (p_wpl v * 4); split; [solve [find_in]| clear - Hzz; lia]| exact I]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx =>
      pose proof (NCD _ Hx) as Y1; pose proof (NCB1 _ Hx) as Y2; cbn [outside]; unfold lined; clear - Y1 Y2 HM0 HM1; repeat split; try exact I; lia) end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK after last line".
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixcmapCreateLinear; 0x9ed54].
    idtac "MARK arm A at cmaplin".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call CML".
    eapply cps_seq.
    { eapply CML with (lo := lo).
      - exact FDO.
      - exact MST.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lenv_tac.
      - unfold lres; rewrite FRSt3, LVT3; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split;
        [ clear - FRB; lia | clear - LVB; lia | clear - CRt3 CRB; unfold RASTER_COST in *; lia
        | intros p9 n9 Hp; cbn [In] in Hp; repeat (destruct Hp as [Hp|Hp]; [injection Hp; intros En Ep; rewrite <- En; first [exact DDN | clear - WPLO; lia | clear; lia] |]); exact (LVP p9 n9 Hp) ]. }
    idtac "MARK CML applied".
    hide FRM. hide FSH. hide PXD. hide PXS.
    after_call RT AF.
    idtac "MARK after_call CML".
    lazymatch goal with A : ART RT ?S ?mm, C : cmap_obj (rt_live RT ?S) ?mm ?cm (mkCmapv ?ca 2 4 4) |- cps _ (ASTA RT ?S _ _) _ =>
      rename S into Σm; rename A into ARTM; rename cm into cmap; rename ca into carr; rename C into CMO end.
    lazymatch goal with H : rt_live RT Σm = _ |- _ => rename H into LVMN end.
    lazymatch goal with H : rw_cells asegs _ carr cmaplin24_cells |- _ => rename H into CAR end.
    assert (LVM : rt_live RT Σm = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVMN, LVT3; reflexivity).
    assert (FRSm : rt_frames RT Σm = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σm = _ |- _ => rewrite E end; exact FRSt3).
    assert (SP0m : rt_sp0 RT Σm = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRm : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σm) by (lazymatch goal with E : rt_credit RT Σt3 <= rt_credit RT Σm |- _ => clear - E CRt3; lia end).
    assert (LSUBm : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σm)) by (intros e He; rewrite LVM; do 9 right; exact He).
    pose proof CMO as ((cpad & CMC) & (CQIN & CQ0 & CQ16 & _) & (KAIN & KA0 & KA16 & _) & COK & CANE). cbn [c_arr c_depth c_nalloc c_n] in KAIN, KA0, KA16, CANE.
    change (4 * 4) with 16 in KAIN.
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK carried CML".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => exact I).
    (* [comment removed for export] *)
    assert (NECM : forall e, In e ((t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> cmap)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σm _ [(carr, 16)] cmap 24 _ e ARTM LVM); [cbn [app]; right; exact He| clear; lia| exact Hn]).
    assert (NECA : forall e, In e ((cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> carr)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σm _ [] carr 16 _ e ARTM LVM); [cbn [app]; exact He| clear; lia| exact Hn]).
    assert (SUBCM : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σm) /\ fst e <> cmap)
      by (intros e He; split; [exact (LSUBm e He)| apply NECM; [do 7 right; exact He| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBCA : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σm) /\ fst e <> carr)
      by (intros e He; split; [exact (LSUBm e He)| apply NECA; [do 8 right; exact He| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (NCCM : forall a, PF a -> a < cmap \/ cmap + 24 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σm _ cmap 24 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTM ltac:(rewrite LVM; right; left; reflexivity) SUBCM);
          [ rewrite FRSm; intros e He; right; exact He | rewrite SP0m; ul | exact (proj1 Ha) ]).
    assert (NCCA : forall a, PF a -> a < carr \/ carr + 16 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σm _ carr 16 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTM ltac:(rewrite LVM; left; reflexivity) SUBCA);
          [ rewrite FRSm; intros e He; right; exact He | rewrite SP0m; ul | exact (proj1 Ha) ]).
    assert (N_cmpd : cmap <> pixd) by (intros E; exact (NECM (pixd, 64) ltac:(do 6 right; left; reflexivity) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_capd : carr <> pixd) by (intros E; exact (NECA (pixd, 64) ltac:(do 7 right; left; reflexivity) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cmda : cmap <> dat) by (intros E; exact (NECM (dat, rs) ltac:(do 5 right; left; reflexivity) DDN (eq_sym E))).
    assert (N_cada : carr <> dat) by (intros E; exact (NECA (dat, rs) ltac:(do 6 right; left; reflexivity) DDN (eq_sym E))).
    assert (N_cmpx : cmap <> pix) by (intros E; exact (NECM (pix, 64) ltac:(do 7 right; exact PIN) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_capx : carr <> pix) by (intros E; exact (NECA (pix, 64) ltac:(do 8 right; exact PIN) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cmsd : cmap <> p_data v) by (intros E; exact (NECM (p_data v, 4 * (p_wpl v * p_h v)) ltac:(do 7 right; exact DIN) DSZ (eq_sym E))).
    assert (N_casd : carr <> p_data v) by (intros E; exact (NECA (p_data v, 4 * (p_wpl v * p_h v)) ltac:(do 8 right; exact DIN) DSZ (eq_sym E))).
    assert (N_cmb1 : cmap <> bufs1) by (intros E; exact (NECM (bufs1, p_wpl v * 4) ltac:(do 4 right; left; reflexivity) ltac:(cbn; clear - WPLO; lia) (eq_sym E))).
    assert (N_cab1 : carr <> bufs1) by (intros E; exact (NECA (bufs1, p_wpl v * 4) ltac:(do 5 right; left; reflexivity) ltac:(cbn; clear - WPLO; lia) (eq_sym E))).
    assert (N_cmb2 : cmap <> bufs2) by (intros E; exact (NECM (bufs2, p_wpl v * 4) ltac:(do 3 right; left; reflexivity) ltac:(cbn; clear - WPLO; lia) (eq_sym E))).
    assert (N_cab2 : carr <> bufs2) by (intros E; exact (NECA (bufs2, p_wpl v * 4) ltac:(do 4 right; left; reflexivity) ltac:(cbn; clear - WPLO; lia) (eq_sym E))).
    assert (N_cmtv : cmap <> tv) by (intros E; exact (NECM (tv, 1024) ltac:(do 2 right; left; reflexivity) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_catv : carr <> tv) by (intros E; exact (NECA (tv, 1024) ltac:(do 3 right; left; reflexivity) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cmt38 : cmap <> t38) by (intros E; exact (NECM (t38, 1024) ltac:(right; left; reflexivity) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cat38 : carr <> t38) by (intros E; exact (NECA (t38, 1024) ltac:(do 2 right; left; reflexivity) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cmt14 : cmap <> t14) by (intros E; exact (NECM (t14, 1024) ltac:(left; reflexivity) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cat14 : carr <> t14) by (intros E; exact (NECA (t14, 1024) ltac:(right; left; reflexivity) ltac:(cbn; clear; lia) (eq_sym E))).
    lazymatch goal with A : ART RT Σm ?mm |- _ =>
      pose proof (live_apart2 RT AF Σm mm pixd 64 cmap 24 A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_cmpd (eq_sym (f_equal fst E))))) as A_pdcm;
      pose proof (live_apart2 RT AF Σm mm pixd 64 carr 16 A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_capd (eq_sym (f_equal fst E))))) as A_pdca;
      pose proof (live_apart2 RT AF Σm mm pix 64 cmap 24 A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_cmpx (eq_sym (f_equal fst E))))) as A_pxcm;
      pose proof (live_apart2 RT AF Σm mm pix 64 carr 16 A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_capx (eq_sym (f_equal fst E))))) as A_pxca end.
    park A_pdcm. park A_pdca. park A_pxcm. park A_pxca.
    chunk_facts RT AF GP cmap 24. chunk_facts RT AF GP carr 16.
    fframe_chunk RT AF fr 2%nat 256 cmap 24. fframe_chunk RT AF fr 2%nat 256 carr 16.
    idtac "MARK CML facts".
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixSetColormap; 0x9ed54].
    idtac "MARK arm A at pixSetColormap".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call PSC".
    set (vf := pv_inf (pv_res v1 v) v).
    unfold hid in HOKD.
    lazymatch goal with PX : rw_cells asegs ?mc pixd _ |- cps _ (ASTA RT Σm _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (PODm : pix_obj (rt_live RT Σm) mc pixd vf (mkCmapv carr 2 4 4))
        by (split; [unfold pix_cells, vf, pv_inf, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP; exact PX|];
            split; [split; [solve [find_in]| split; [exact PD0| split; [exact PD16| clear; lia]]]|];
            split; [exact HOKD|];
            split; [right; split; [split; [solve [find_in]| split; [exact DD0| split; [exact DD16| exact DDN]]]| unfold parked in DDNE; exact DDNE]| left; exact VCMAP]);
      assert (CMOm : cmap_obj (rt_live RT Σm) mc cmap (mkCmapv carr 2 4 4))
        by (split; [exists cpad; exact CMC| split; [split; [solve [find_in]| split; [exact CQ0| split; [exact CQ16| clear; lia]]]| split; [split; [cbn [c_arr c_nalloc]; solve [find_in]| split; [exact KA0| split; [exact KA16| cbn; clear; lia]]]| split; [exact COK| exact CANE]]]]) end.
    hide HOKD.
    idtac "MARK PSC objs".
    eapply cps_seq.
    { eapply PSC with (lo := lo) (pix := pixd) (cmap := cmap) (v := vf) (cv := mkCmapv carr 2 4 4).
      - exact FDO.
      - exact MST.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact PODm.
      - exact VCMAP.
      - exact VDATA1.
      - exact CMOm.
      - exact N_cmpd.
      - cbn [c_arr]. exact N_capd.
      - exact N_cmda.
      - cbn [c_arr]. exact N_cada.
      - lenv_tac.
      - unfold lres; rewrite FRSm, LVM; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split;
        [ clear - FRB; lia | clear - LVB; lia | clear - CRm CRB; unfold RASTER_COST in *; lia
        | intros p9 n9 Hp; cbn [In] in Hp; repeat (destruct Hp as [Hp|Hp]; [injection Hp; intros En Ep; rewrite <- En; first [exact DDN | clear - WPLO; lia | clear; lia] |]); exact (LVP p9 n9 Hp) ]. }
    idtac "MARK PSC applied".
    clear PODm CMOm.
    hide FRM. hide FSH. hide PXS. hide CAR. hide CMC. clear PXD.
    after_call RT AF.
    idtac "MARK after_call PSC".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σs; rename A into ARTS end.
    lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
    unfold pix_cells, vf, pv_inf, pv_res in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD in PXD. fold dat in PXD.
    assert (LVS : rt_live RT Σs = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σs = _ |- _ => rewrite E end; exact LVM).
    assert (FRSs : rt_frames RT Σs = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σs = _ |- _ => rewrite E end; exact FRSm).
    assert (SP0s : rt_sp0 RT Σs = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRs : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σs) by (lazymatch goal with E : rt_credit RT Σm - 6 <= rt_credit RT Σs |- _ => clear - E CRm; lia end).
    assert (LSUBs : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σs)) by (intros e He; rewrite LVS; do 9 right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => repeat match goal with Hf : parked (fr + 256 <= pixd \/ _ <= fr) |- _ => unfold parked in Hf; revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => repeat match goal with Hf : parked (pixd + _ <= fr / 8 + 2147450880 \/ (fr + 256) / 8 + 2147450880 <= pixd) |- _ => unfold parked in Hf; revert Hf end; unfold shad, SHB in *; clear - Hx FR64; intros; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in DSP; clear - Hx DSP; repeat split; try exact I; lia);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| unfold cmaplin24_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; exact Hx]) ltac:(fun Hx => unfold parked in A_pdca; unfold cmaplin24_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; clear - Hx A_pdca; repeat split; try exact I; lia);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| unfold cmap_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; exact Hx]) ltac:(fun Hx => unfold parked in A_pdcm; unfold cmap_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; clear - Hx A_pdcm; repeat split; try exact I; lia) end.
    idtac "MARK carried PSC".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; pose proof (NCP _ (conj Hx1 Hx2)) as Y; clear - Y; repeat split; try exact I; lia).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK after PSC".
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9e494].
    idtac "MARK arm A at free 1".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    unfold cmaplin24_cells in CAR. unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC.
    assert (NRB1 : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> bufs1)
      by (intros e He; apply (NEB1 e He); destruct He as [<-|[<-|He]]; [exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (NRB2 : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> bufs2)
      by (intros e He; apply (NEB2 e); [right; exact He|]; destruct He as [<-|[<-|He]]; [exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (NRT1 : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> tv)
      by (intros e He; apply (NET1 e); [do 2 right; exact He|]; destruct He as [<-|[<-|He]]; [exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (NRT2 : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> t38)
      by (intros e He; apply (NET2 e); [do 3 right; exact He|]; destruct He as [<-|[<-|He]]; [exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (NRT3 : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> t14)
      by (intros e He; apply (NET3 e); [do 4 right; exact He|]; destruct He as [<-|[<-|He]]; [exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    park_ne.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call free 1".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf1 : In (0x9ed5c :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := bufs1) (n := p_wpl v * 4); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVS; do 6 right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf1]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK free 1 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf1; rename A into ARTF1 end.
    assert (LVF1 : rt_live RT Σf1 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf1 = _ |- _ => rewrite E end; rewrite LVS; rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cab1); rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmb1); rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b1t14)); rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b1t38)); rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b1tv)); rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b1b2)); rewrite (live_remove_hd bufs1 _ _ NRB1); reflexivity).
    assert (FRSf1 : rt_frames RT Σf1 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf1 = _ |- _ => rewrite E end; assumption).
    assert (SP0f1 : rt_sp0 RT Σf1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf1 : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σf1) by (repeat match goal with E : rt_credit RT Σf1 = _ |- _ => rewrite E end; exact CRs).
    assert (LSUBf1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf1)) by (intros e He; rewrite LVF1; repeat right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK carried f1".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf1| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9e494].
    idtac "MARK arm A after free 1".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call free 2".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf2 : In (0x9ed64 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := bufs2) (n := p_wpl v * 4); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVF1; do 5 right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf2]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK free 2 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf2; rename A into ARTF2 end.
    assert (LVF2 : rt_live RT Σf2 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf2 = _ |- _ => rewrite E end; rewrite LVF1; rewrite (live_remove_cons' bufs2); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cab2); rewrite (live_remove_cons' bufs2); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmb2); rewrite (live_remove_cons' bufs2); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b2t14)); rewrite (live_remove_cons' bufs2); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b2t38)); rewrite (live_remove_cons' bufs2); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b2tv)); rewrite (live_remove_hd bufs2 _ _ NRB2); reflexivity).
    assert (FRSf2 : rt_frames RT Σf2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf2 = _ |- _ => rewrite E end; assumption).
    assert (SP0f2 : rt_sp0 RT Σf2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf2 : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σf2) by (repeat match goal with E : rt_credit RT Σf2 = _ |- _ => rewrite E end; exact CRf1).
    assert (LSUBf2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf2)) by (intros e He; rewrite LVF2; repeat right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK carried f2".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf2| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9e494].
    idtac "MARK arm A after free 2".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call free 3".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf3 : In (0x9ed6c :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := tv) (n := 1024); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVF2; do 4 right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf3]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK free 3 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf3; rename A into ARTF3 end.
    assert (LVF3 : rt_live RT Σf3 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf3 = _ |- _ => rewrite E end; rewrite LVF2; rewrite (live_remove_cons' tv); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_catv); rewrite (live_remove_cons' tv); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmtv); rewrite (live_remove_cons' tv); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_tvt14)); rewrite (live_remove_cons' tv); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_tvt38)); rewrite (live_remove_hd tv _ _ NRT1); reflexivity).
    assert (FRSf3 : rt_frames RT Σf3 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf3 = _ |- _ => rewrite E end; assumption).
    assert (SP0f3 : rt_sp0 RT Σf3 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf3 : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σf3) by (repeat match goal with E : rt_credit RT Σf3 = _ |- _ => rewrite E end; exact CRf2).
    assert (LSUBf3 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf3)) by (intros e He; rewrite LVF3; repeat right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK carried f3".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf3| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9e494].
    idtac "MARK arm A after free 3".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call free 4".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf4 : In (0x9ed74 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := t38) (n := 1024); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVF3; do 3 right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf4]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK free 4 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf4; rename A into ARTF4 end.
    assert (LVF4 : rt_live RT Σf4 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf4 = _ |- _ => rewrite E end; rewrite LVF3; rewrite (live_remove_cons' t38); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cat38); rewrite (live_remove_cons' t38); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmt38); rewrite (live_remove_cons' t38); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_t38t14)); rewrite (live_remove_hd t38 _ _ NRT2); reflexivity).
    assert (FRSf4 : rt_frames RT Σf4 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf4 = _ |- _ => rewrite E end; assumption).
    assert (SP0f4 : rt_sp0 RT Σf4 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf4 : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σf4) by (repeat match goal with E : rt_credit RT Σf4 = _ |- _ => rewrite E end; exact CRf3).
    assert (LSUBf4 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf4)) by (intros e He; rewrite LVF4; repeat right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK carried f4".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf4| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9e494].
    idtac "MARK arm A after free 4".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call free 5".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf5 : In (0x9ed7c :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := t14) (n := 1024); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVF4; do 2 right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf5]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK free 5 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf5; rename A into ARTF5 end.
    assert (LVF5 : rt_live RT Σf5 = (carr, 16) :: (cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf5 = _ |- _ => rewrite E end; rewrite LVF4; rewrite (live_remove_cons' t14); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cat14); rewrite (live_remove_cons' t14); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmt14); rewrite (live_remove_hd t14 _ _ NRT3); reflexivity).
    assert (FRSf5 : rt_frames RT Σf5 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf5 = _ |- _ => rewrite E end; assumption).
    assert (SP0f5 : rt_sp0 RT Σf5 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf5 : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σf5) by (repeat match goal with E : rt_credit RT Σf5 = _ |- _ => rewrite E end; exact CRf4).
    assert (LSUBf5 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf5)) by (intros e He; rewrite LVF5; repeat right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK carried f5".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf5| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDestroy; 0x9e494].
    idtac "MARK arm A after free 5".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call PDR".
    (* [comment removed for export] *)
    split_at FRM 10%nat PPC. split_at PPC 1%nat FRMb.
    pose proof FSH as SH10. split_at SH10 10%nat SH10b. split_at SH10b 1%nat SH10c. clear SH10 SH10c.
    lazymatch goal with PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σf5 _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (POS4 : pix_obj_rc (rt_live RT Σf5) mc pix v cv 2) by (exact (PSRC (rt_live RT Σf5) 2 mc LSUBf5 AGF PS));
      assert (OPP : optrL RT (rt_live RT Σf5) Σf5 mc (fr + 80) 8)
        by (unfold optrL, accok; split;
            [ right; exists fr, 2%nat; rewrite FRSf5; change (fs_size 2) with 256;
              split; [left; reflexivity|]; split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FR0; lia|];
              split; [clear - FRHI SP0R1; lia|];
              replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
              destruct SH10b as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B
            | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; unfold SEGTOP_A; split; [clear - FRSH; unfold parked in FRSH; lia| clear - FRSEG; unfold parked in FRSEG; lia] ]) end.
    idtac "MARK destroy args".
    assert (CR1 : 1 <= rt_credit RT Σf5) by (clear - CRf5 CRB; unfold RASTER_COST in *; lia).
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
    - unfold lres; rewrite FRSf5, LVF5; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [clear - FRB; lia| clear - LVB; lia| exact CR1|
        intros p9 n9 Hp; cbn [In] in Hp; repeat (destruct Hp as [Hp|Hp]; [injection Hp; intros En Ep; rewrite <- En; first [exact DDN | clear - WPLO; lia | clear; lia] |]); exact (LVP p9 n9 Hp)].
    }
    idtac "MARK PDR applied".
    clear POS4 OPP CR1 SH10b.
    hide FRM. hide FRMb. hide FSH. hide PXD. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σz; rename A into ARTZ end.
    assert (LVZ : rt_live RT Σz = (carr, 16) :: (cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σz = _ |- _ => rewrite E end; exact LVF5).
    assert (FRSz : rt_frames RT Σz = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σz = _ |- _ => rewrite E end; exact FRSf5).
    assert (SP0z : rt_sp0 RT Σz = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRz : rt_credit RT Σ - (2 * RASTER_COST + 32) <= rt_credit RT Σz) by (lazymatch goal with E : rt_credit RT Σf5 - 1 <= rt_credit RT Σz |- _ => clear - E CRf5; lia end).
    assert (LSUBz : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σz)) by (intros e He; rewrite LVZ; do 4 right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => unfold parked in FCD; clear - Hx FCD; lia);
      carry AGx FRMb ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => unfold parked in FCD; clear - Hx FCD; lia);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia])
                    ltac:(fun Hx => unfold parked in FCS, FRSH; unfold shad, SHB in *; clear - Hx FCS FR64 FRSH CKH; first [lia | Z.div_mod_to_equations; lia]);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in FCD1, DSP; clear - Hx FCD1 DSP; lia);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => cside carr Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => cside cmap Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0) end.
    idtac "MARK carried z".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; cbn [outside] in Hx2; destruct (NFA _ (conj Hx1 Hx2)) as [N1 N2]; clear - N1 Hx2; repeat split; try exact I; lia).
    lazymatch goal with H : rw_cells asegs _ pix (pix_cells_rc v (2 - 1)) |- _ => rename H into PXS end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    (* [comment removed for export] *)
    unfold hid in SUBP, SUBD.
    assert (SUBP' : forall e, In e (rt_live RT Σ) -> fst e <> pixd) by (intros e He; exact (proj2 (SUBP e He))).
    assert (SUBD' : forall e, In e (rt_live RT Σ) -> fst e <> dat) by (intros e He; exact (proj2 (SUBD e He))).
    clear SUBP SUBD.
    assert (PDINz : In (pixd, 64) (rt_live RT Σz)) by (rewrite LVZ; do 3 right; left; reflexivity).
    assert (DDINz : In (dat, rs) (rt_live RT Σz)) by (rewrite LVZ; do 2 right; left; reflexivity).
    assert (PINz : In (pix, 64) (rt_live RT Σz)) by (rewrite LVZ; do 4 right; exact PIN).
    assert (DINz : In (p_data v, 4 * (p_wpl v * p_h v)) (rt_live RT Σz)) by (rewrite LVZ; do 4 right; exact DIN).
    assert (CMINz : In (cmap, 24) (rt_live RT Σz)) by (rewrite LVZ; right; left; reflexivity).
    assert (CAINz : In (carr, 16) (rt_live RT Σz)) by (rewrite LVZ; left; reflexivity).
    unfold hid in SUBCM, SUBCA.
    assert (SUBCM' : forall e, In e (rt_live RT Σ) -> fst e <> cmap) by (intros e He; exact (proj2 (SUBCM e He))).
    assert (SUBCA' : forall e, In e (rt_live RT Σ) -> fst e <> carr) by (intros e He; exact (proj2 (SUBCA e He))).
    clear SUBCM SUBCA.
    sigma_gc RT Σ Σz.
    repeat match goal with H : In (?b, _) (rt_live RT Σ) |- _ => lazymatch b with pix => fail | p_data v => fail | _ => clear H end end.
    idtac "MARK diet".
    try forget_junk FR; try forget_junk FRM; try forget_junk FSH; try forget_junk FRMb.
    hide PXS. hide PXD. hide CAR. hide CMC.
    (* [comment removed for export] *)
    split_at FR 5%nat FRD. split_at FRD 10%nat FRT.
    lazymatch type of FRD with rw_cells _ ?mq ?A ?cs => destruct (rw_cells_forget asegs mq A cs FRD) as [jdead FRD']; clear FRD; cbn [cells_size csize Nat.add] in FRD' end.
    join_cells FR FRD'. join_cells FR FRT.
    repeat match goal with H : context [bufs1] |- _ => clear H end.
    repeat match goal with H : context [bufs2] |- _ => clear H end.
    repeat match goal with H : context [tv] |- _ => clear H end.
    repeat match goal with H : context [t38] |- _ => clear H end.
    repeat match goal with H : context [t14] |- _ => clear H end.
    repeat match goal with H : context [lined] |- _ => clear H end.
    clear lined. try clear bufs1. try clear bufs2. try clear tv. try clear t38. try clear t14.
    repeat match goal with H : wmono _ _ ?b |- _ => lazymatch goal with |- context [b] => fail | _ => clear H end end.
    repeat match goal with H : munch _ _ ?b |- _ => lazymatch goal with |- context [b] => fail | _ => clear H end end.
    idtac "MARK diet 2".
    (* [comment removed for export] *)
    clear_acc.
    hide FCD. hide FCS. hide CKH. hide FCD1. hide FCS1. hide CKH1. hide DDNE. hide CANE. hide N_cmpd. hide N_cmda. hide N_capd. hide N_cada. hide VDATA1. hide FRSH.
    repeat match goal with H : parked ?T |- _ =>
      lazymatch T with context [fr] => lazymatch T with context [cmap] => hide H | context [carr] => hide H | _ => clear H end | _ => clear H end end.
    unfold hid in FRSH. unpark FRSH.
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9e4f0].
    idtac "MARK at flag load".
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    idtac "MARK at pokes".
    try unfold hid in FRM. try unfold hid in FSH. split_at FRM 1%nat FRMr.
    Time (eapply evt_cut;
    [ eapply EVQ_exit;
      [ eapply d2bpp_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
      | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
    | ]).
    clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold d2bpp_exit_W, SHB in MUx. unfold d2bpp_sh_f5 in FSH.
    idtac "MARK pokes applied".
    Time loop_art RT AF Σz mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    Time (lazymatch type of MUx with munch _ ?ma ?mb =>
      loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *; clear - Hx FRHI FRSH FRSEG LOW LOR FR64 FR0 SP0R1 SP0R0 SP0W; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end).
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => unfold parked in FCD, CKH, FRSH; unfold shad, SHB in *; clear - Hx FCD CKH FRSH FRHI SP0R0 SP0R1 CKR LOW LOR FR64 FR0; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
      carry_mu MUx PXD ltac:(fun Hx => unfold parked in FCD1, CKH1, FRSH; unfold shad, SHB in *; clear - Hx FCD1 CKH1 FRSH FRHI SP0R0 SP0R1 CKR1 LOW LOR FR64 FR0; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
      carry_mu MUx CAR ltac:(fun Hx => cside carr Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0);
      carry_mu MUx CMC ltac:(fun Hx => cside cmap Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0) end.
    hide PXS. hide PXD. hide CAR. hide CMC.
    repeat match goal with H : parked _ |- _ => hide H end.
    join_cells FRM FRMr.
    idtac "MARK carried x".
    frame_release_g RT AF GP MST Σ fr 2%nat 256 PF AGF PFS usp lo 0x9e5a4
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => agf_side PFS NFA LOR Hx) ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
    idtac "MARK frame released".
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    lazymatch goal with MUx : munch [(?fl, ?fl + 1)] _ ?mb |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => repeat match goal with Hf : fl < pix \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx PXD ltac:(fun Hx => repeat match goal with Hf : fl < pixd \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx CAR ltac:(fun Hx => repeat match goal with Hf : fl < carr \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx CMC ltac:(fun Hx => repeat match goal with Hf : fl < cmap \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia) end.
    hide PXS. hide PXD. hide CAR. hide CMC.
    clear_acc. refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp)] [0x9e5fc].
    (* [comment removed for export] *)
    try change (Z_to_bv 64 (bv_unsigned sp + -288)) with (Z_to_bv 64 (usp + -288)).
    awalk (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -304) |- _ => release_frame FR ST' usp end.
    lazymatch goal with MUx : munch _ _ ?mb |- evt _ _ (MS _ _ _ _ _ ?mb _) =>
      carry_mu MUx PXS ltac:(fun Hx => clear - Hx CKR LOW LOR; repeat split; try exact I; lia);
      carry_mu MUx PXD ltac:(fun Hx => clear - Hx CKR1 LOW LOR; repeat split; try exact I; lia);
      carry_mu MUx CAR ltac:(fun Hx => cside carr Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0);
      carry_mu MUx CMC ltac:(fun Hx => cside cmap Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0) end.
    cps_stop.
    idtac "MARK epilogue walked".
    apply cps_finish; intros c Hc; subst QF; unfold d2bpp_post; cbv beta.
    set (vg := mkPixv (p_w vf) (p_h vf) (p_d vf) (p_spp vf) (p_wpl vf) (p_xres vf) (p_yres vf) (p_inf vf) (p_spec vf) cmap (p_data vf)).
    assert (VGC : p_cmap vg = cmap) by reflexivity.
    assert (VGD : p_data vg = dat) by reflexivity.
    assert (CMNZ : cmap <> 0) by (clear - CQ0; lia).
    unfold hid in HOKD, CAR, CMC.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, pixd, vg, (mkCmapv carr 2 4 4) end.
    split.
    2: {
    split; [intros Z0; exfalso; clear - Z0 PD0; lia|].
    split.
    { intros _. rewrite LV2, LVZ.
      assert (CA0' : carr <> 0) by (clear - KA0; lia).
      unfold parked in N_cmpd, N_cmda, N_capd, N_cada, CANE.
      pose proof (live_destroy_tmpl (rt_live RT Σ) pixd dat rs cmap carr 16 vg (mkCmapv carr 2 4 4) VGD VGC
                    (fun _ => eq_refl) VDATA1 ltac:(unfold parked in DDNE; exact DDNE)
                    (fun _ => conj CA0' (conj N_cmpd (conj N_cmda (conj N_capd (conj N_cada CANE)))))
                    (fun e He => conj (SUBP' e He) (SUBD' e He)) (fun _ e He => conj (SUBCM' e He) (SUBCA' e He))) as LD.
      rewrite (proj2 (Z.eqb_neq cmap 0) CMNZ) in LD. exact LD. }
    split.
    { intros p9 n9 Hp. rewrite LV2, LVZ in Hp. cbn [In] in Hp. repeat (destruct Hp as [Hp|Hp]; [injection Hp; intros En Ep; rewrite <- En; first [exact DDN | clear; lia] |]). exact (LVP p9 n9 Hp). }
    split; [rewrite LV2, LVZ; cbn [length]; clear; lia|].
    split; [exact FRS2|]. split; [rewrite SP2; exact SP0z|].
    unfold D2_COST, OP_COST, is_d8. cbn [Z.eqb Pos.eqb].
    rewrite CR2. clear - CRz. unfold RASTER_COST in *. lia.
    }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    split; [unfold lpost_f, rt_after_f; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); split; [split; [assumption| split; assumption]| split; assumption]|].
    split; [unfold keepsL, rt_pres_fp; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
    split.
    { rewrite LV2, LVZ. lazymatch goal with PS : rw_cells asegs ?mc pix _ |- pix_obj _ ?mc _ _ _ =>
        exact (PSRC ((carr, 16) :: (cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) 1 mc ltac:(intros e He; do 4 right; exact He) AGF PS) end. }
    right. split; [| rewrite VGD; exact VDATA1].
    rewrite LV2, LVZ.
    split; [unfold pix_cells, vg, vf, pv_inf, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD; exact PXD|].
    split; [split; [do 3 right; left; reflexivity| split; [exact PD0| split; [exact PD16| clear; lia]]]|].
    split; [exact HOKD|].
    split; [right; split; [split; [do 2 right; left; reflexivity| split; [exact DD0| split; [exact DD16| exact DDN]]]| unfold parked in DDNE; exact DDNE]|].
    right. cbn [c_arr]. split; [| split; [exact N_cmpd| split; [exact N_capd| split; [rewrite VGD; exact N_cmda| rewrite VGD; exact N_cada]]]].
    split; [exists cpad; unfold cmap_cells; cbn [c_arr c_depth c_nalloc c_n]; exact CMC|].
    split; [split; [right; left; reflexivity| split; [exact CQ0| split; [exact CQ16| clear; lia]]]|].
    split; [split; [cbn [c_arr c_nalloc]; left; reflexivity| split; [exact KA0| split; [exact KA16| cbn; clear; lia]]]|].
    split; [exact COK| exact CANE].
  (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    rename CKR3 into CKRT, CKS3 into CKST, CKH3 into CKHT, FCD3 into FCDT, FCS3 into FCST, CKR4 into CKRU, CKS4 into CKSU, CKH4 into CKHU, FCD4 into FCDU, FCS4 into FCSU.
    lazymatch goal with A : ART RT Σp ?mm |- _ =>
      pose proof (live_apart2 RT AF Σp mm pix 64 pixt 64 A PINp PTIN ltac:(intros E; injection E; intros E1; exact (NST E1))) as DSXT;
      pose proof (live_apart2 RT AF Σp mm pix 64 dtt rst A PINp DTIN ltac:(intros E; injection E; intros _ E1; exact (NSDT E1))) as DSDT;
      pose proof (live_apart2 RT AF Σp mm pixd 64 pixt 64 A PDINp PTIN ltac:(intros E; injection E; intros E1; exact (NPT E1))) as DPXT;
      pose proof (live_apart2 RT AF Σp mm pixd 64 dtt rst A PDINp DTIN ltac:(intros E; injection E; intros _ E1; exact (NPDT E1))) as DPDT;
      pose proof (live_apart2 RT AF Σp mm pixt 64 dtt rst A PTIN DTIN ltac:(intros E; injection E; intros _ E1; unfold parked in DTNE; exact (DTNE (eq_sym E1)))) as DTT end.
    hide POT. hide POSp. hide HOKT. hide SUBT. hide SUBDT.
    assert (EWT : p_wpl vt = p_wpl v) by (rewrite EWS, HWPL, D8; reflexivity).
    rewrite EWT in PXT, ERST, RSTB, EWS.   (* [comment removed for export] *)
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK arm B start".
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9e494].
    idtac "MARK arm B at calloc 1".
    assert (WPLO : 0 < p_wpl v) by (rewrite EWS; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    assert (WPHI : p_wpl v <= 5001) by (rewrite EWS; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    rewrite !(sx32_small (p_wpl v)) by (clear - WPLO WPHI; lia).
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 1".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc1 : In (0x9e0c4 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT Σp _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
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
    assert (LVB1 : rt_live RT Σb1 = (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVB1N, LVPB; reflexivity).
    assert (FRSb1 : rt_frames RT Σb1 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σb1 = _ |- _ => rewrite E end; exact FRSp).
    assert (SP0b1 : rt_sp0 RT Σb1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRb1 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σb1) by (repeat match goal with E : rt_credit RT Σb1 = _ |- _ => rewrite E end; exact CRp).
    lazymatch goal with H : 0 < bufs1 |- _ => rename H into B10 end.
    lazymatch goal with H : bufs1 mod 16 = 0 |- _ => rename H into B116 end.
    chunk_facts RT AF GP bufs1 (p_wpl v * 4). fframe_chunk RT AF fr 2%nat 256 bufs1 (p_wpl v * 4).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9e494].
    idtac "MARK arm B at calloc 2".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 2".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc2 : In (0x9e0d8 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
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
    assert (LVB2 : rt_live RT Σb2 = (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVB2N, LVB1; reflexivity).
    assert (FRSb2 : rt_frames RT Σb2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σb2 = _ |- _ => rewrite E end; exact FRSb1).
    assert (SP0b2 : rt_sp0 RT Σb2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRb2 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σb2) by (repeat match goal with E : rt_credit RT Σb2 = _ |- _ => rewrite E end; exact CRb1).
    lazymatch goal with H : 0 < bufs2 |- _ => rename H into B20 end.
    lazymatch goal with H : bufs2 mod 16 = 0 |- _ => rename H into B216 end.
    chunk_facts RT AF GP bufs2 (p_wpl v * 4). fframe_chunk RT AF fr 2%nat 256 bufs2 (p_wpl v * 4).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9e494].
    idtac "MARK arm B at calloc 3".
  (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 3".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc3 : In (0x9e100 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 256) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRc3]
           | |- _ => first [ unfold CALLOC_MAX; clear; lia
                           | rewrite LVB2; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                           | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
           end. }
    idtac "MARK calloc 3 applied".
    clear UCC.
    after_call RT AF.
    change (256 * 4)%Z with 1024%Z in *.
    fold_pres usp.
    idtac "MARK after calloc 3".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σt1; rename A into ARTT1 end.
    lazymatch goal with H : rt_live RT Σt1 = (?p, _) :: _ |- _ => rename H into LVT1N; rename p into tv end.
    lazymatch goal with H : rw_cells asegs _ tv [CB _ _] |- _ => rename H into T1Z end.
    assert (LVT1 : rt_live RT Σt1 = (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVT1N, LVB2; reflexivity).
    assert (FRSt1 : rt_frames RT Σt1 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σt1 = _ |- _ => rewrite E end; assumption).
    assert (SP0t1 : rt_sp0 RT Σt1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRt1 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σt1) by (repeat match goal with E : rt_credit RT Σt1 = _ |- _ => rewrite E end; assumption).
    lazymatch goal with H : 0 < tv |- _ => rename H into T10 end.
    lazymatch goal with H : tv mod 16 = 0 |- _ => rename H into T116 end.
    chunk_facts RT AF GP tv 1024. fframe_chunk RT AF fr 2%nat 256 tv 1024.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9e15c].
    idtac "MARK arm B at calloc 4".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 4".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc4 : In (0x9e110 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 256) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRc4]
           | |- _ => first [ unfold CALLOC_MAX; clear; lia
                           | rewrite LVT1; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                           | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
           end. }
    idtac "MARK calloc 4 applied".
    clear UCC.
    after_call RT AF.
    change (256 * 4)%Z with 1024%Z in *.
    fold_pres usp.
    idtac "MARK after calloc 4".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σt2; rename A into ARTT2 end.
    lazymatch goal with H : rt_live RT Σt2 = (?p, _) :: _ |- _ => rename H into LVT2N; rename p into t38 end.
    lazymatch goal with H : rw_cells asegs _ t38 [CB _ _] |- _ => rename H into T2Z end.
    assert (LVT2 : rt_live RT Σt2 = (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVT2N, LVT1; reflexivity).
    assert (FRSt2 : rt_frames RT Σt2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σt2 = _ |- _ => rewrite E end; assumption).
    assert (SP0t2 : rt_sp0 RT Σt2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRt2 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σt2) by (repeat match goal with E : rt_credit RT Σt2 = _ |- _ => rewrite E end; assumption).
    lazymatch goal with H : 0 < t38 |- _ => rename H into T20 end.
    lazymatch goal with H : t38 mod 16 = 0 |- _ => rename H into T216 end.
    chunk_facts RT AF GP t38 1024. fframe_chunk RT AF fr 2%nat 256 t38 1024.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_calloc; 0x9e15c].
    idtac "MARK arm B at calloc 5".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call calloc 5".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRc5 : In (0x9e120 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 256) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRc5]
           | |- _ => first [ unfold CALLOC_MAX; clear; lia
                           | rewrite LVT2; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                           | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
           end. }
    idtac "MARK calloc 5 applied".
    clear UCC.
    after_call RT AF.
    change (256 * 4)%Z with 1024%Z in *.
    fold_pres usp.
    idtac "MARK after calloc 5".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σt3; rename A into ARTT3 end.
    lazymatch goal with H : rt_live RT Σt3 = (?p, _) :: _ |- _ => rename H into LVT3N; rename p into t14 end.
    lazymatch goal with H : rw_cells asegs _ t14 [CB _ _] |- _ => rename H into T3Z end.
    assert (LVT3 : rt_live RT Σt3 = (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVT3N, LVT2; reflexivity).
    assert (FRSt3 : rt_frames RT Σt3 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σt3 = _ |- _ => rewrite E end; assumption).
    assert (SP0t3 : rt_sp0 RT Σt3 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRt3 : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σt3) by (repeat match goal with E : rt_credit RT Σt3 = _ |- _ => rewrite E end; assumption).
    lazymatch goal with H : 0 < t14 |- _ => rename H into T30 end.
    lazymatch goal with H : t14 mod 16 = 0 |- _ => rename H into T316 end.
    chunk_facts RT AF GP t14 1024. fframe_chunk RT AF fr 2%nat 256 t14 1024.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9e124; e_calloc].
    idtac "MARK arm B tables stored".
    try forget_junk FR; try forget_junk FRM; try forget_junk FSH; try forget_junk FRMb.
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx => agf_side PFS NFA LOR Hx) end.
    assert (NEB1 : forall e, In e ((dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> bufs1)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σb1 _ [] bufs1 (p_wpl v * 4) _ e ARTB1 LVB1); [cbn [app]; exact He| clear - WPLO; lia| exact Hn]).
    assert (NEB2 : forall e, In e ((bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> bufs2)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σb2 _ [] bufs2 (p_wpl v * 4) _ e ARTB2 LVB2); [cbn [app]; exact He| clear - WPLO; lia| exact Hn]).
    assert (NET1 : forall e, In e ((bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> tv)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σt1 _ [] tv 1024 _ e ARTT1 LVT1); [cbn [app]; exact He| clear; lia| exact Hn]).
    assert (NET2 : forall e, In e ((tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> t38)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σt2 _ [] t38 1024 _ e ARTT2 LVT2); [cbn [app]; exact He| clear; lia| exact Hn]).
    assert (NET3 : forall e, In e ((t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> t14)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σt3 _ [] t14 1024 _ e ARTT3 LVT3); [cbn [app]; exact He| clear; lia| exact Hn]).
    assert (SUBB1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σb1) /\ fst e <> bufs1)
      by (intros e He; split; [rewrite LVB1; solve [find_in]| apply NEB1; [solve [find_in]| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBB2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σb2) /\ fst e <> bufs2)
      by (intros e He; split; [rewrite LVB2; solve [find_in]| apply NEB2; [solve [find_in]| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBT1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt1) /\ fst e <> tv)
      by (intros e He; split; [rewrite LVT1; solve [find_in]| apply NET1; [solve [find_in]| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBT2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt2) /\ fst e <> t38)
      by (intros e He; split; [rewrite LVT2; solve [find_in]| apply NET2; [solve [find_in]| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBT3 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt3) /\ fst e <> t14)
      by (intros e He; split; [rewrite LVT3; solve [find_in]| apply NET3; [solve [find_in]| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (NCB1 : forall a, PF a -> a < bufs1 \/ bufs1 + p_wpl v * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σb1 _ bufs1 (p_wpl v * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTB1 ltac:(rewrite LVB1; left; reflexivity) SUBB1);
          [ rewrite FRSb1; intros e He; right; exact He | rewrite SP0b1; ul | exact (proj1 Ha) ]).
    assert (NCB2 : forall a, PF a -> a < bufs2 \/ bufs2 + p_wpl v * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σb2 _ bufs2 (p_wpl v * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTB2 ltac:(rewrite LVB2; left; reflexivity) SUBB2);
          [ rewrite FRSb2; intros e He; right; exact He | rewrite SP0b2; ul | exact (proj1 Ha) ]).
    assert (NCT1 : forall a, PF a -> a < tv \/ tv + 1024 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σt1 _ tv 1024 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTT1 ltac:(rewrite LVT1; left; reflexivity) SUBT1);
          [ rewrite FRSt1; intros e He; right; exact He | rewrite SP0t1; ul | exact (proj1 Ha) ]).
    assert (NCT2 : forall a, PF a -> a < t38 \/ t38 + 1024 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σt2 _ t38 1024 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTT2 ltac:(rewrite LVT2; left; reflexivity) SUBT2);
          [ rewrite FRSt2; intros e He; right; exact He | rewrite SP0t2; ul | exact (proj1 Ha) ]).
    assert (NCT3 : forall a, PF a -> a < t14 \/ t14 + 1024 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σt3 _ t14 1024 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTT3 ltac:(rewrite LVT3; left; reflexivity) SUBT3);
          [ rewrite FRSt3; intros e He; right; exact He | rewrite SP0t3; ul | exact (proj1 Ha) ]).
    (* [comment removed for export] *)
    assert (N_b1b2 : bufs1 <> bufs2) by (exact (NEB2 (bufs1, p_wpl v * 4) ltac:(solve [find_in]) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_b1tv : bufs1 <> tv) by (exact (NET1 (bufs1, p_wpl v * 4) ltac:(solve [find_in]) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_b2tv : bufs2 <> tv) by (exact (NET1 (bufs2, p_wpl v * 4) ltac:(solve [find_in]) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_b1t38 : bufs1 <> t38) by (exact (NET2 (bufs1, p_wpl v * 4) ltac:(solve [find_in]) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_b2t38 : bufs2 <> t38) by (exact (NET2 (bufs2, p_wpl v * 4) ltac:(solve [find_in]) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_tvt38 : tv <> t38) by (exact (NET2 (tv, 1024) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_b1t14 : bufs1 <> t14) by (exact (NET3 (bufs1, p_wpl v * 4) ltac:(solve [find_in]) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_b2t14 : bufs2 <> t14) by (exact (NET3 (bufs2, p_wpl v * 4) ltac:(solve [find_in]) ltac:(cbn [snd]; clear - WPLO; lia))).
    assert (N_tvt14 : tv <> t14) by (exact (NET3 (tv, 1024) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_t38t14 : t38 <> t14) by (exact (NET3 (t38, 1024) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_pxb1 : pix <> bufs1) by (exact (NEB1 (pix, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_pxb2 : pix <> bufs2) by (exact (NEB2 (pix, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_pxtv : pix <> tv) by (exact (NET1 (pix, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_pxt38 : pix <> t38) by (exact (NET2 (pix, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_pxt14 : pix <> t14) by (exact (NET3 (pix, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_pdb1 : pixd <> bufs1) by (exact (NEB1 (pixd, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_pdb2 : pixd <> bufs2) by (exact (NEB2 (pixd, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_pdtv : pixd <> tv) by (exact (NET1 (pixd, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_pdt38 : pixd <> t38) by (exact (NET2 (pixd, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_pdt14 : pixd <> t14) by (exact (NET3 (pixd, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_dab1 : dat <> bufs1) by (exact (NEB1 (dat, rs) ltac:(solve [find_in]) DDN)).
    assert (N_dab2 : dat <> bufs2) by (exact (NEB2 (dat, rs) ltac:(solve [find_in]) DDN)).
    assert (N_datv : dat <> tv) by (exact (NET1 (dat, rs) ltac:(solve [find_in]) DDN)).
    assert (N_dat38 : dat <> t38) by (exact (NET2 (dat, rs) ltac:(solve [find_in]) DDN)).
    assert (N_dat14 : dat <> t14) by (exact (NET3 (dat, rs) ltac:(solve [find_in]) DDN)).
    assert (N_sdb1 : p_data v <> bufs1) by (exact (NEB1 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(solve [find_in]) DSZ)).
    assert (N_sdb2 : p_data v <> bufs2) by (exact (NEB2 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(solve [find_in]) DSZ)).
    assert (N_sdtv : p_data v <> tv) by (exact (NET1 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(solve [find_in]) DSZ)).
    assert (N_sdt38 : p_data v <> t38) by (exact (NET2 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(solve [find_in]) DSZ)).
    assert (N_sdt14 : p_data v <> t14) by (exact (NET3 (p_data v, 4 * (p_wpl v * p_h v)) ltac:(solve [find_in]) DSZ)).
    assert (N_ttb1 : pixt <> bufs1) by (exact (NEB1 (pixt, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_ttb2 : pixt <> bufs2) by (exact (NEB2 (pixt, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_tttv : pixt <> tv) by (exact (NET1 (pixt, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_ttt38 : pixt <> t38) by (exact (NET2 (pixt, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_ttt14 : pixt <> t14) by (exact (NET3 (pixt, 64) ltac:(solve [find_in]) ltac:(cbn [snd]; clear; lia))).
    assert (N_dtb1 : dtt <> bufs1) by (exact (NEB1 (dtt, rst) ltac:(solve [find_in]) DTN)).
    assert (N_dtb2 : dtt <> bufs2) by (exact (NEB2 (dtt, rst) ltac:(solve [find_in]) DTN)).
    assert (N_dttv : dtt <> tv) by (exact (NET1 (dtt, rst) ltac:(solve [find_in]) DTN)).
    assert (N_dtt38 : dtt <> t38) by (exact (NET2 (dtt, rst) ltac:(solve [find_in]) DTN)).
    assert (N_dtt14 : dtt <> t14) by (exact (NET3 (dtt, rst) ltac:(solve [find_in]) DTN)).
    idtac "MARK diseqs".
    lazymatch goal with A : ART RT Σt3 ?mm |- _ =>
      pose proof (live_apart2 RT AF Σt3 mm (pix) (64) (bufs1) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pxb1 (f_equal fst E)))) as A_pxb1;
      pose proof (live_apart2 RT AF Σt3 mm (pix) (64) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pxb2 (f_equal fst E)))) as A_pxb2;
      pose proof (live_apart2 RT AF Σt3 mm (pix) (64) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pxtv (f_equal fst E)))) as A_pxtv;
      pose proof (live_apart2 RT AF Σt3 mm (pix) (64) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pxt38 (f_equal fst E)))) as A_pxt38;
      pose proof (live_apart2 RT AF Σt3 mm (pix) (64) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pxt14 (f_equal fst E)))) as A_pxt14;
      pose proof (live_apart2 RT AF Σt3 mm (pixd) (64) (bufs1) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pdb1 (f_equal fst E)))) as A_pdb1;
      pose proof (live_apart2 RT AF Σt3 mm (pixd) (64) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pdb2 (f_equal fst E)))) as A_pdb2;
      pose proof (live_apart2 RT AF Σt3 mm (pixd) (64) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pdtv (f_equal fst E)))) as A_pdtv;
      pose proof (live_apart2 RT AF Σt3 mm (pixd) (64) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pdt38 (f_equal fst E)))) as A_pdt38;
      pose proof (live_apart2 RT AF Σt3 mm (pixd) (64) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_pdt14 (f_equal fst E)))) as A_pdt14;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (bufs1) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dab1 (f_equal fst E)))) as A_dab1;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dab2 (f_equal fst E)))) as A_dab2;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_datv (f_equal fst E)))) as A_datv;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dat38 (f_equal fst E)))) as A_dat38;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dat14 (f_equal fst E)))) as A_dat14;
      pose proof (live_apart2 RT AF Σt3 mm (p_data v) (4 * (p_wpl v * p_h v)) (bufs1) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_sdb1 (f_equal fst E)))) as A_sdb1;
      pose proof (live_apart2 RT AF Σt3 mm (p_data v) (4 * (p_wpl v * p_h v)) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_sdb2 (f_equal fst E)))) as A_sdb2;
      pose proof (live_apart2 RT AF Σt3 mm (p_data v) (4 * (p_wpl v * p_h v)) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_sdtv (f_equal fst E)))) as A_sdtv;
      pose proof (live_apart2 RT AF Σt3 mm (p_data v) (4 * (p_wpl v * p_h v)) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_sdt38 (f_equal fst E)))) as A_sdt38;
      pose proof (live_apart2 RT AF Σt3 mm (p_data v) (4 * (p_wpl v * p_h v)) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_sdt14 (f_equal fst E)))) as A_sdt14;
      pose proof (live_apart2 RT AF Σt3 mm (bufs1) (p_wpl v * 4) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b1b2 (f_equal fst E)))) as A_b1b2;
      pose proof (live_apart2 RT AF Σt3 mm (bufs1) (p_wpl v * 4) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b1tv (f_equal fst E)))) as A_b1tv;
      pose proof (live_apart2 RT AF Σt3 mm (bufs1) (p_wpl v * 4) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b1t38 (f_equal fst E)))) as A_b1t38;
      pose proof (live_apart2 RT AF Σt3 mm (bufs1) (p_wpl v * 4) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b1t14 (f_equal fst E)))) as A_b1t14;
      pose proof (live_apart2 RT AF Σt3 mm (bufs2) (p_wpl v * 4) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b2tv (f_equal fst E)))) as A_b2tv;
      pose proof (live_apart2 RT AF Σt3 mm (bufs2) (p_wpl v * 4) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b2t38 (f_equal fst E)))) as A_b2t38;
      pose proof (live_apart2 RT AF Σt3 mm (bufs2) (p_wpl v * 4) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_b2t14 (f_equal fst E)))) as A_b2t14;
      pose proof (live_apart2 RT AF Σt3 mm (tv) (1024) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_tvt38 (f_equal fst E)))) as A_tvt38;
      pose proof (live_apart2 RT AF Σt3 mm (tv) (1024) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_tvt14 (f_equal fst E)))) as A_tvt14;
      pose proof (live_apart2 RT AF Σt3 mm (pixt) (64) (bufs1) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_ttb1 (f_equal fst E)))) as A_ttb1;
      pose proof (live_apart2 RT AF Σt3 mm (pixt) (64) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_ttb2 (f_equal fst E)))) as A_ttb2;
      pose proof (live_apart2 RT AF Σt3 mm (pixt) (64) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_tttv (f_equal fst E)))) as A_tttv;
      pose proof (live_apart2 RT AF Σt3 mm (pixt) (64) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_ttt38 (f_equal fst E)))) as A_ttt38;
      pose proof (live_apart2 RT AF Σt3 mm (pixt) (64) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_ttt14 (f_equal fst E)))) as A_ttt14;
      pose proof (live_apart2 RT AF Σt3 mm (dtt) (rst) (bufs1) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dtb1 (f_equal fst E)))) as A_dtb1;
      pose proof (live_apart2 RT AF Σt3 mm (dtt) (rst) (bufs2) (p_wpl v * 4) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dtb2 (f_equal fst E)))) as A_dtb2;
      pose proof (live_apart2 RT AF Σt3 mm (dtt) (rst) (tv) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dttv (f_equal fst E)))) as A_dttv;
      pose proof (live_apart2 RT AF Σt3 mm (dtt) (rst) (t38) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dtt38 (f_equal fst E)))) as A_dtt38;
      pose proof (live_apart2 RT AF Σt3 mm (dtt) (rst) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_dtt14 (f_equal fst E)))) as A_dtt14;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (dtt) (rst) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (NDDT (f_equal fst E)))) as A_dadt;
      pose proof (live_apart2 RT AF Σt3 mm (dat) (rs) (pixt) (64) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (NDT (f_equal fst E)))) as A_datt;
      pose proof (live_apart2 RT AF Σt3 mm (t38) (1024) (t14) (1024) A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_t38t14 (f_equal fst E)))) as A_t38t14 end.
    park A_pxb1. park A_pxb2. park A_pxtv. park A_pxt38. park A_pxt14. park A_pdb1. park A_pdb2. park A_pdtv. park A_pdt38. park A_pdt14. park A_dab1. park A_dab2. park A_datv. park A_dat38. park A_dat14. park A_sdb1. park A_sdb2. park A_sdtv. park A_sdt38. park A_sdt14. park A_b1b2. park A_b1tv. park A_b1t38. park A_b1t14. park A_b2tv. park A_b2t38. park A_b2t14. park A_tvt38. park A_tvt14. park A_t38t14.
    park A_ttb1. park A_ttb2. park A_tttv. park A_ttt38. park A_ttt14. park A_dtb1. park A_dtb2. park A_dttv. park A_dtt38. park A_dtt14. park A_dadt. park A_datt.
    idtac "MARK apartness".
    assert (GEO : dt2_geom tv t38 t14 (usp + -304 + 152)).
    { unfold dt2_geom, SEGTOP_A. unfold parked in CKS5, CKH5, CKS6, CKH6, CKS7, CKH7, A_tvt38, A_tvt14, A_t38t14.
      clear - T10 T116 T20 T216 T30 T316 CKR5 CKR6 CKR7 CKS5 CKS6 CKS7 CKH5 CKH6 CKH7 SP0R1 A_tvt38 A_tvt14 A_t38t14 LOW LOR USP0 SPA SPT AL STa.
      repeat lazymatch goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia]. }
    park_disj.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32); (tv, tv + 1024); (t38, t38 + 1024); (t14, t14 + 1024)] [0x9e15c; e_calloc].
    idtac "MARK arm B at table loop".
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof T1Z as U1; apply u8arr_of_rw_cells in U1; destruct (u8arr_u32arr mm tv _ 256 U1 ltac:(rewrite repeat_length; clear; lia)) as (ws1 & UA1 & UAL1); clear U1;
      pose proof T2Z as U2; apply u8arr_of_rw_cells in U2; destruct (u8arr_u32arr mm t38 _ 256 U2 ltac:(rewrite repeat_length; clear; lia)) as (ws2 & UA2 & UAL2); clear U2;
      pose proof T3Z as U3; apply u8arr_of_rw_cells in U3; destruct (u8arr_u32arr mm t14 _ 256 U3 ltac:(rewrite repeat_length; clear; lia)) as (ws3 & UA3 & UAL3); clear U3 end.
    pose proof FR as CA. split_at CA 14%nat CA2. split_at CA2 1%nat CA3. clear CA CA3.
    lazymatch type of CA2 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 152) in CA2 by (clear; lia) end.
    idtac "MARK table premises".
    eapply evt_cut.
    { lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        epose proof (dt2_tables 256%nat 0 _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm mm (usp + -304) tv t38 t14 ws1 ws2 ws3
                       ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia) GEO (munch_refl [(tv, tv + 1024); (t38, t38 + 1024); (t14, t14 + 1024)] mm) (wmono_refl asegs mm) MIx
                       UA1 UAL1 ltac:(assumption) UA2 UAL2 ltac:(assumption) UA3 UAL3 ltac:(assumption) CA2) as ZR end.
      unfold SHB in ZR. exact ZR. }
    idtac "MARK tables applied".
    intros ms' PO. unfold dt2_exit in PO.
    destruct PO as (ra' & a0' & a1' & a2' & a5' & a6' & s3' & s6' & s7' & t6' & mt & ws1' & ws2' & ws3' & -> & MUt & WMt & MIt & UA1' & UAL1' & ACC1' & UA2' & UAL2' & ACC2' & UA3' & UAL3' & ACC3' & CAt).
    idtac "MARK tables post".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT. clear B1Z B2Z T1Z T2Z T3Z UA1 UA2 UA3 UAL1 UAL2 UAL3 CA2.
    loop_art RT AF Σt3 mt lo MUt ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; right; right; left; exists tv, 1024; split; [solve [find_in]| clear - Hzz; lia]| split; [intros zz Hzz; right; right; left; exists t38, 1024; split; [solve [find_in]| clear - Hzz; lia]| split; [intros zz Hzz; right; right; left; exists t14, 1024; split; [solve [find_in]| clear - Hzz; lia]| exact I]]]]]]).
    idtac "MARK tables loop_art".
    lazymatch type of MUt with munch _ ?ma ?mb =>
      loop_transport ma mb MUt ltac:(fun Hx => clear - Hx CKR5 CKR6 CKR7 CKS5 CKS6 CKS7 LOW LOR STa SP0R0; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
    idtac "MARK tables loop_transport".
    carry_mu MUt FRM ltac:(fun Hx => unfold parked in FCD5, FCD6, FCD7; clear - Hx FCD5 FCD6 FCD7; repeat split; try exact I; lia).
    carry_mu MUt FSH ltac:(fun Hx => unfold parked in FCS5, FCS6, FCS7; clear - Hx FCS5 FCS6 FCS7 FR64; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    carry_mu MUt PXD ltac:(fun Hx => unfold parked in A_pdtv, A_pdt38, A_pdt14; clear - Hx A_pdtv A_pdt38 A_pdt14; repeat split; try exact I; lia).
    carry_mu MUt PXS ltac:(fun Hx => unfold parked in A_pxtv, A_pxt38, A_pxt14; clear - Hx A_pxtv A_pxt38 A_pxt14; repeat split; try exact I; lia).
    carry_mu MUt PXT ltac:(fun Hx => unfold parked in A_tttv, A_ttt38, A_ttt14; clear - Hx A_tttv A_ttt38 A_ttt14; repeat split; try exact I; lia).
    idtac "MARK tables carried".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; right; right; left; exists tv, 1024; split; [solve [find_in]| clear - Hzz; lia]| split; [intros zz Hzz; right; right; left; exists t38, 1024; split; [solve [find_in]| clear - Hzz; lia]| split; [intros zz Hzz; right; right; left; exists t14, 1024; split; [solve [find_in]| clear - Hzz; lia]| exact I]]]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx =>
      pose proof (NCT1 _ Hx) as Y1; pose proof (NCT2 _ Hx) as Y2; pose proof (NCT3 _ Hx) as Y3; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [Hx1 Hx2];
      cbn [outside]; unfold shad, SHB in *; clear - P1 N1 N2 Hx2 LOR Y1 Y2 Y3; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK after tables".
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_asan_memcpy; 0x9e15c].
    idtac "MARK arm B at memcpy 1".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite ?(sx32_small (p_w v)) by (clear - HW0 HW2; lia). rewrite ?(sx32_small (p_h v)) by (clear - HH0 HH2; lia).
    rewrite ?(bv_swrap_small 32 (p_wpl v * 4)) by (change (bv_half_modulus 32) with (2^31); clear - WPLO WPHI; lia).
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK at_call memcpy 1".
    assert (NLE : p_wpl v * 4 <= 4 * (p_wpl v * p_h v)) by (clear - WPLO HH0; nia).
    assert (NLEt : p_wpl v * 4 <= rst) by (rewrite ERST; exact NLE).
    lazymatch goal with A : ART RT Σt3 ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (af_acc_live RT AF Σt3 mm dtt rst A ltac:(solve [find_in])) as (WRS & ACCS);
      pose proof (af_acc_live RT AF Σt3 mm bufs2 (p_wpl v * 4) A ltac:(solve [find_in])) as (WR2 & ACCB) end.
    apply wr_at_rw_CB in WRS; [| clear - DTN; lia]. destruct WRS as (sbs & SBC).
    pose proof SBC as [[[SBL _] _] _]. cbn in SBL.
    apply u8arr_of_rw_cells in SBC. destruct SBC as [SB _].
    rewrite <- (firstn_skipn (Z.to_nat (p_wpl v * 4)) sbs) in SB. apply bytes_at_app in SB. destruct SB as [SB1 _].
    assert (SBL1 : Z.of_nat (length (firstn (Z.to_nat (p_wpl v * 4)) sbs)) = p_wpl v * 4) by (rewrite firstn_length_le; [clear - WPLO; lia| rewrite SBL; clear - WPLO NLEt; lia]).
    assert (Q7a : 0 <= bufs2 <= 2^47) by (clear - CKR4 SP0R1 B20 WPLO; lia).
    assert (Q7b : 0 <= dtt <= 2^47) by (clear - CKRU SP0R1 DT0 DTN; lia).
    assert (Q3 : bufs2 + p_wpl v * 4 <= dtt \/ dtt + p_wpl v * 4 <= bufs2) by (unfold parked in A_dtb2; clear - A_dtb2 NLEt; lia).
    assert (Q4 : dtt + p_wpl v * 4 <= lo) by (clear - CKRU LOW NLEt; lia).
    eapply cps_seq.
    { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
      eapply MC0 with (lo := lo) (d := bufs2) (s := dtt) (bs := firstn (Z.to_nat (p_wpl v * 4)) sbs); rewrite ?SBL1.
      all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; clear - WPLO; lia
         | |- bytes_at _ _ _ _ => exact SB1
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ => unfold checked_src; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
             split; [intros _; split; [eapply acc_sub; [exact ACCS| clear; lia | clear - NLEt; lia] | left; exists dtt, rst; split; [solve [find_in]| clear - NLEt WPLO; lia]] | left; exact Q4]
         | |- checked_dst _ _ _ _ _ _ => unfold checked_dst; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
             split; [intros _; split; [exact ACCB| left; exists bufs2, (p_wpl v * 4); split; [solve [find_in]| clear; lia]]|];
             split; [intros i Hi; right; right; left; exists bufs2, (p_wpl v * 4); split; [solve [find_in]| clear - Hi; lia]| exact WR2]
         | |- call_ok _ _ _ _ _ => call_ok_tac2 SPA
         | |- _ \/ _ => exact Q3
         | |- (_ <= _ <= _) => first [exact Q7a | exact Q7b]
         | |- (_ < _) => clear - WPLO WPHI; lia
         | |- ?g => idtac "LEFT:" g
         end. }
    idtac "MARK memcpy 1 applied".
    rewrite SBL1. clear SB1 SBL1 ACCS ACCB WR2.
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT. try clear B1Z B2Z.
    after_call RT AF.
    idtac "MARK after_call memcpy 1".
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => fr_side fr Hx);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => sh_side fr FR64 Hx);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in A_pdb2; clear - Hx A_pdb2; lia);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in A_pxb2; clear - Hx A_pxb2; lia);
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in A_ttb2; clear - Hx A_ttb2; lia) end.
    idtac "MARK carried memcpy 1".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; pose proof (NCB2 _ (conj Hx1 Hx2)) as Y; clear - Y; lia).
    repeat match goal with H : bytes_at asegs _ bufs2 _ |- _ => clear H end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK after memcpy 1".
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9e66c; e_asan_memcpy].
    idtac "MARK arm B at h test".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (WPLD1 : 0 < p_wpl v1) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    assert (WPLD2 : p_wpl v1 <= 1251) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
    rewrite ?(bv_swrap_small 32 (p_h v + -1)) by (change (bv_half_modulus 32) with (2^31); clear - HH0 HH2; lia).
    rewrite ?(bv_swrap_small 32 (p_h v + -1)) in FR by (change (bv_half_modulus 32) with (2^31); clear - HH0 HH2; lia).
    rewrite ?(bv_swrap_small 32 (p_wpl v * 4)) in FR by (change (bv_half_modulus 32) with (2^31); clear - WPLO WPHI; lia).
    rewrite ?(sx32_small (p_wpl v1)) in FR by (clear - WPLD1 WPLD2; lia).
    replace (p_wpl v * 4) with (4 * p_wpl v) in FR by (clear; lia).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx => agf_side PFS NFA LOR Hx) end.
    lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      set (JC := d2_join RT Σt3 PMc gp sp (usp + -304) 304 lo fr (fr / 8 + 2147450880) (p_w v) (p_h v) (p_wpl v) (p_wpl v1) dtt dat rs bufs1 bufs2 (p_wpl v * 4) tv t38 t14 40%nat
                 [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] mm); rename mm into mh end.
    idtac "MARK B JC set".
    eapply cps_seq with (Q := JC).
    {
    walk_to AF MST [(usp - 368, usp)] [0x9e66c].
    lstep.
    destruct (Z.eq_dec (p_h v) 1) as [HONE|HTWO].
    + (* [comment removed for export] *)
      brT.
      awalk [0x9eae4; 0x9e6a8].
      rewrite ?(bv_swrap_small 32 (p_w v + -1)) by (change (bv_half_modulus 32) with (2^31); clear - HW0 HW2; lia).
      cps_stop.
      idtac "MARK B h1 at join".
      apply cps_finish. intros c Hc. subst JC. unfold d2_join. eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-.
      pose proof FR as F1. split_at F1 6%nat F2. split_at F2 10%nat F3.
      lazymatch type of F2 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 56) in F2 by (clear; lia) end.
      lazymatch type of F3 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 160) in F3 by (clear; lia) end.
      forget_cells F1 0%nat 2%nat. forget_cells F3 0%nat 3%nat.
      do 24 eexists.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
      apply agree_refl.
    + (* [comment removed for export] *)
      brF.
      awalk [0x9e6a8].
      idtac "MARK B h2 at rows".
      rewrite ?(bv_swrap_small 32 (p_w v + -1)) by (change (bv_half_modulus 32) with (2^31); clear - HW0 HW2; lia).
      rewrite ?(bv_swrap_small 32 (p_w v + -1)) in FR by (change (bv_half_modulus 32) with (2^31); clear - HW0 HW2; lia).
      replace (Z.land (p_w v + -1) 18446744073709551615) with (p_w v + -1) in FR
        by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); symmetry; apply Z.mod_small; clear - HW0 HW2; lia).
      replace (Z.land ((p_w v + -1) * 4294967296) 18446744073709551615) with ((p_w v + -1) * 4294967296) in FR
        by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); symmetry; apply Z.mod_small; clear - HW0 HW2; lia).
      replace ((p_w v + -1) * 4294967296 / 4294967296) with (p_w v + -1) in FR by (symmetry; apply Z.div_mul; clear; lia).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      assert (GEOM : d2r_geom (rt_sp0 RT Σt3) lo (usp + -304) dat rs dtt rst bufs1 bufs2 (p_wpl v * 4) (p_wpl v) (p_wpl v1) (p_w v) (p_h v) tv t38 t14).
      { rewrite SP0t3. unfold d2r_geom, LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A.
        assert (QG1 : p_wpl v1 <= p_wpl v) by (rewrite EWD, EWS; apply Z.div_le_mono; clear - HW0; lia).
        assert (QG2 : p_w v <= 4 * p_wpl v) by (rewrite EWS; clear - HW0; Z.div_mod_to_equations; lia).
        assert (QG3 : p_w v <= 16 * p_wpl v1) by (rewrite EWD; clear - HW0; Z.div_mod_to_equations; lia).
        assert (QG4 : 0 < rs <= 4 * (p_wpl v * p_h v)) by (rewrite ERS; clear - QG1 WPLD1 HH0; nia).
        clear - QG1 QG2 QG3 QG4 WPLO WPHI WPLD1 WPLD2 HW0 HW2 HH0 HH2 HRS0 HRS1 NLE ERS ERST DTN DD0 DD16 CKR2 CKS2 CKH2 DT0 DT16 CKRU CKSU CKHU B10 B116 CKR3 CKS3 CKH3 B20 B216 CKR4 CKS4 CKH4
                T10 T116 CKR5 CKS5 CKH5 T20 T216 CKR6 CKS6 CKH6 T30 T316 CKR7 CKS7 CKH7 DRD A_dab1 A_dab2 A_dtb1 A_dtb2 A_dadt A_b1b2 A_datv A_b1tv A_b2tv A_dat38 A_b1t38 A_b2t38 A_dat14 A_b1t14 A_b2t14
                LOW LOR SPT SPA AL SPB SP0R0 SP0R1 SP0W STa USP0.
        repeat lazymatch goal with |- _ /\ _ => split end; por. }
      idtac "MARK B GEOM".
      pose proof FR as F1. split_at F1 6%nat F2. split_at F2 13%nat F3.
      lazymatch type of F2 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 56) in F2 by (clear; lia) end.
      lazymatch type of F3 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 160) in F3 by (clear; lia) end.
      hide F1. hide F3. hide FRM. hide FSH. hide PXD. hide PXS. hide PXT. clear FR.
      eapply cps_seq.
      { eapply (d2_rows RT AF GP RC (Z.to_nat (p_h v - 1)) 0) with (lo := lo) (rd := rs) (rs := rst) (n1 := p_wpl v * 4) (wpls := p_wpl v) (wpld := p_wpl v1)
               (w := p_w v) (h := p_h v) (datad := dat) (datas := dtt) (t14 := t14) (ic := Z_to_bv 64 (fr + 48)).
        all: lazymatch goal with
          | |- Z.of_nat _ = _ => clear - HH0 HTWO; lia
          | |- 0 <= 0 => clear; lia
          | |- (1 <= _)%nat => clear - HH0 HTWO; lia
          | |- fdfs_only _ => exact FDO
          | |- mat_stable _ => exact MST
          | |- d2r_geom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact GEOM
          | |- In _ _ => solve [find_in]
          | |- ART _ _ _ => assumption
          | |- mem_inv _ _ => assumption
          | |- stk _ _ _ _ => assumption
          | |- LIBH _ => assumption
          | |- io_ssp _ => assumption
          | |- rw_cells _ _ _ _ => exact F2
          | |- ?g => idtac "LEFT:" g
          end. }
      idtac "MARK B rows applied".
      clear F2 GEOM.
      unfold d2r_post. after_call RT AF.
      idtac "MARK B rows opened".
      lazymatch goal with H : rw_cells asegs _ _ (d2r_frame _ _ _ _ _ _ _ _ _ _) |- _ => rename H into FBK; unfold d2r_frame in FBK end.
      lazymatch goal with H : agree_on (d2r_keep _ _ _ _ _ _ _ _) ?ma ?mb |- _ => rename H into AGR; rename ma into mh2 end.
      unfold d2r_keep in AGR.
      carry AGR F1 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR2 CKR3 CKR4 LOW LOR; repeat split; try exact I; lia).
      carry AGR F3 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SPT; lia) ltac:(fun Hx => clear - Hx CKR2 CKR3 CKR4 LOW LOR; repeat split; try exact I; lia).
      idtac "MARK B rows carried".
      pose proof FBK as FBKn. norm_cells FBKn.   (* [comment removed for export] *)
      walk_to AF MST [(usp - 368, usp)] [0x9eae4].
      cps_stop. clear FBKn.
      idtac "MARK B h2 at join".
      apply cps_finish. intros c Hc. subst JC. unfold d2_join. eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-.
      forget_cells F1 0%nat 2%nat. forget_cells FBK 0%nat 4%nat. forget_cells F3 0%nat 3%nat.
      do 24 eexists.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [exact F1|]. split; [exact FBK|]. split; [exact F3|].
      lazymatch goal with MUx : munch _ mh mh2 |- agree_on _ mh ?m3 =>
        apply (agree_trans _ mh mh2 m3);
        [ eapply agree_sub; [exact (agree_of_munch _ mh mh2 _ MUx (fun x Hx => Hx))|]; cbv beta; intros a9 [Ha91 Ha92]; cbn [outside] in Ha92; cbn [outside];
          destruct (aclient_split RT AF Σt3 _ (usp + -304) a9 ltac:(eassumption) Ha91) as [Q|Q]; (split; [| exact I]); unfold STACK_WIN in *; clear - Q Ha92 LOW LOR SP0t3; lia
        | eapply agree_sub; [exact AGR|]; cbv beta; intros a9 [Ha91 Ha92]; split; [exact Ha91| cbn [outside] in Ha92; cbn [outside]; clear - Ha92; repeat split; try exact I; lia] ] end.
    }
    idtac "MARK B joined".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    subst JC. unfold d2_join. after_call RT AF.
    idtac "MARK B J opened".
    lazymatch goal with A : ART RT Σt3 ?mq |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mq _))) _ => rename A into ARTJ; rename mq into mj end.
    lazymatch goal with H : rw_cells asegs mj (usp + -304) _ |- _ => rename H into F1 end.
    lazymatch goal with H : rw_cells asegs mj (usp + -304 + 56) _ |- _ => rename H into F2 end.
    lazymatch goal with H : rw_cells asegs mj (usp + -304 + 160) _ |- _ => rename H into F3 end.
    lazymatch goal with H : agree_on _ mh mj |- _ => rename H into AGJ end.
    clear FR.
    carry AGJ FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia])
      ltac:(fun Hx => repeat match goal with Hf : parked (fr + 256 <= ?b \/ _ <= fr) |- _ => unfold parked in Hf; revert Hf end; clear - Hx FRHI LOW LOR; intros; repeat split; try exact I; lia).
    carry AGJ FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia])
      ltac:(fun Hx => repeat match goal with Hf : parked (?b + _ <= fr / 8 + 2147450880 \/ (fr + 256) / 8 + 2147450880 <= ?b) |- _ => unfold parked in Hf; revert Hf end;
                      unfold shad, SHB in *; clear - Hx FR64 FRHI SP0R1 SP0W LOW LOR; intros; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    carry AGJ PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx])
      ltac:(fun Hx => unfold parked in DPD, A_pdb1, A_pdb2; clear - Hx DPD A_pdb1 A_pdb2 CKR1 LOW LOR; repeat split; try exact I; lia).
    carry AGJ PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx])
      ltac:(fun Hx => unfold parked in DSD, A_pxb1, A_pxb2; clear - Hx DSD A_pxb1 A_pxb2 CKR LOW LOR; repeat split; try exact I; lia).
    carry AGJ PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [solve [find_in]| exact Hx])
      ltac:(fun Hx => unfold parked in A_datt, A_ttb1, A_ttb2; clear - Hx A_datt A_ttb1 A_ttb2 CKRT LOW LOR; repeat split; try exact I; lia).
    idtac "MARK B J carried".
    assert (AGF2 : agree_on PF m mj).
    { apply (agree_trans PF m mh mj AGF). eapply agree_sub; [exact AGJ|]. cbv beta. intros a9 Ha9.
      pose proof (PFS _ Ha9) as P9. pose proof (NCD _ Ha9) as Y1. pose proof (NCB1 _ Ha9) as Y2. pose proof (NCB2 _ Ha9) as Y3.
      destruct Ha9 as [Ha91 Ha92]. split.
      - apply (aclient_mono _ _ usp _ _ _ _ Ha91); [intros e He; rewrite LVT3; do 9 right; exact He| rewrite FRSt3; intros e He; right; exact He| clear; lia].
      - cbn [outside]. clear - P9 Y1 Y2 Y3 ERS LOR. repeat split; try exact I; lia. }
    clear AGF AGJ. rename AGF2 into AGF.
    join_cells F1 F2. join_cells F1 F3. rename F1 into FR.
    repeat match goal with H : context [mh] |- _ => clear H end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK B after join".
    try forget_junk FR; try forget_junk FRM; try forget_junk FSH; try forget_junk FRMb.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_asan_memcpy].
    idtac "MARK arm B at memcpy L".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK B at_call memcpy L".
    lazymatch goal with A : ART RT Σt3 ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (af_acc_live RT AF Σt3 mm bufs2 (p_wpl v * 4) A ltac:(solve [find_in])) as (WRS & ACCS);
      pose proof (af_acc_live RT AF Σt3 mm bufs1 (p_wpl v * 4) A ltac:(solve [find_in])) as (WRB & ACCB) end.
    apply wr_at_rw_CB in WRS; [| clear - WPLO; lia]. destruct WRS as (cbs & SBC).
    pose proof SBC as [[[SBL2 _] _] _]. cbn in SBL2.
    apply u8arr_of_rw_cells in SBC. destruct SBC as [SB2 _].
    assert (SBL1 : Z.of_nat (length cbs) = p_wpl v * 4) by (rewrite SBL2; clear - WPLO; lia).
    assert (Q8a : 0 <= bufs1 <= 2^47) by (clear - CKR3 SP0R1 B10 WPLO; lia).
    assert (Q8b : 0 <= bufs2 <= 2^47) by (clear - CKR4 SP0R1 B20 WPLO; lia).
    assert (Q6 : bufs1 + p_wpl v * 4 <= bufs2 \/ bufs2 + p_wpl v * 4 <= bufs1) by (unfold parked in A_b1b2; clear - A_b1b2; lia).
    assert (Q5 : bufs2 + p_wpl v * 4 <= lo) by (clear - CKR4 LOW; lia).
    eapply cps_seq.
    { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
      eapply MC0 with (lo := lo) (d := bufs1) (s := bufs2) (bs := cbs); rewrite ?SBL1.
      all: lazymatch goal with
           | |- fdfs_only _ => exact FDO
           | |- mat_stable _ => exact MST
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; clear - WPLO; lia
           | |- bytes_at _ _ _ _ => exact SB2
           | |- ART _ _ _ => assumption
           | |- mem_inv _ _ => assumption
           | |- checked_src _ _ _ _ _ _ _ =>
               unfold checked_src; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
               split; [intros _; split; [exact ACCS | left; exists bufs2, (p_wpl v * 4); split; [solve [find_in]| clear; lia]] | left; exact Q5]
           | |- checked_dst _ _ _ _ _ _ =>
               unfold checked_dst; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
               split; [intros _; split; [exact ACCB| left; exists bufs1, (p_wpl v * 4); split; [solve [find_in]| clear; lia]]|];
               split; [intros i0 Hi; right; right; left; exists bufs1, (p_wpl v * 4); split; [solve [find_in]| clear - Hi; lia]| exact WRB]
           | |- call_ok _ _ _ _ _ => call_ok_tac2 SPA
           | |- _ \/ _ => exact Q6
           | |- (_ <= _ <= _) => first [exact Q8a | exact Q8b]
           | |- (_ < _) => clear - WPLO WPHI; lia
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK B memcpy L applied".
    rewrite SBL1. clear SB2 SBL1 SBL2 ACCS ACCB WRB.
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT.
    after_call RT AF.
    idtac "MARK B after_call memcpy L".
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => fr_side fr Hx);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => sh_side fr FR64 Hx);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in A_pdb1; clear - Hx A_pdb1; lia);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in A_pxb1; clear - Hx A_pxb1; lia);
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in A_ttb1; clear - Hx A_ttb1; lia) end.
    idtac "MARK B carried memcpy L".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; pose proof (NCB1 _ (conj Hx1 Hx2)) as Y; clear - Y; lia).
    lazymatch goal with H : bytes_at asegs ?mm bufs1 cbs |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ => rename H into CB1 end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK B after memcpy L".
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9eb14].
    idtac "MARK arm B at last line".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite ?(bv_swrap_small 32 ((p_h v - 1) * p_wpl v1)) by (change (bv_half_modulus 32) with (2^31); clear - HH0 HH2 WPLD1 WPLD2; nia).
    replace (Z.land ((p_h v - 1) * p_wpl v1) 18446744073709551615) with ((p_h v - 1) * p_wpl v1)
      by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); symmetry; apply Z.mod_small; clear - HH0 HH2 WPLD1 WPLD2; nia).
    assert (HM0 : 0 <= (p_h v - 1) * p_wpl v1 * 4) by (clear - HH0 WPLD1; nia).
    assert (HM1 : (p_h v - 1) * p_wpl v1 * 4 + 4 * p_wpl v1 = rs) by (rewrite ERS; clear; lia).
    set (lined := dat + (p_h v - 1) * p_wpl v1 * 4) in *.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx => agf_side PFS NFA LOR Hx) end.
    clear_acc. refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    (* [comment removed for export] *)
    assert (L1 : 0 < lined) by (unfold lined; clear - DD0 HM0; lia).
    assert (L2 : lined mod 4 = 0) by (unfold lined; clear - DD16 HM0; Z.div_mod_to_equations; lia).
    assert (L3 : lined + 4 * p_wpl v1 <= 2^47) by (unfold lined; clear - CKR2 SP0R1 HM0 HM1; lia).
    assert (L4 : lined + 4 * p_wpl v1 <= 0x7fff7000 \/ 0x10007fff8000 <= lined) by (unfold lined; unfold parked in CKH2; clear - CKH2 HM0 HM1; lia).
    assert (L5 : lined + 4 * p_wpl v1 <= 0x10000 \/ 6569984 <= lined) by (unfold lined; unfold parked in CKS2; clear - CKS2 HM0 HM1; lia).
    assert (L6 : bufs1 + p_wpl v * 4 <= lined \/ lined + 4 * p_wpl v1 <= bufs1) by (unfold lined; unfold parked in A_dab1; clear - A_dab1 HM0 HM1; lia).
    assert (L7 : bufs2 + p_wpl v * 4 <= lined \/ lined + 4 * p_wpl v1 <= bufs2) by (unfold lined; unfold parked in A_dab2; clear - A_dab2 HM0 HM1; lia).
    assert (L8 : tv + 1024 <= lined \/ lined + 4 * p_wpl v1 <= tv) by (unfold lined; unfold parked in A_datv; clear - A_datv HM0 HM1; lia).
    assert (L9 : t38 + 1024 <= lined \/ lined + 4 * p_wpl v1 <= t38) by (unfold lined; unfold parked in A_dat38; clear - A_dat38 HM0 HM1; lia).
    assert (L10 : t14 + 1024 <= lined \/ lined + 4 * p_wpl v1 <= t14) by (unfold lined; unfold parked in A_dat14; clear - A_dat14 HM0 HM1; lia).
    assert (L11 : p_w v <= p_wpl v * 4) by (rewrite EWS; clear - HW0; Z.div_mod_to_equations; lia).
    assert (L12 : p_w v <= 4 * (4 * p_wpl v1)) by (rewrite EWD; clear - HW0; Z.div_mod_to_equations; lia).
    assert (L13 : bufs2 + p_wpl v * 4 <= bufs1 \/ bufs1 + p_wpl v * 4 <= bufs2) by (unfold parked in A_b1b2; clear - A_b1b2; lia).
    assert (GEO1 : d2_geom lined (4 * p_wpl v1) bufs1 bufs2 (p_wpl v * 4) tv t38 t14 (p_w v)).
    { unfold d2_geom, SEGTOP_A.
      clear - L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 HW0 HW2 WPLO WPHI WPLD1 WPLD2 B10 B116 CKR3 CKS3 CKH3 B20 B216 CKR4 CKS4 CKH4
              T10 T116 CKR5 CKS5 CKH5 T20 T216 CKR6 CKS6 CKH6 T30 T316 CKR7 CKS7 CKH7 A_b1tv A_b2tv A_b1t38 A_b2t38 A_b1t14 A_b2t14 SP0R1.
      repeat lazymatch goal with |- _ /\ _ => split end; por. }
    idtac "MARK B GEO1".
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT Σt3 ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (af_acc_live RT AF Σt3 mm bufs1 (p_wpl v * 4) A ltac:(solve [find_in])) as (WQB & AQB);
      pose proof (af_acc_live RT AF Σt3 mm dat rs A ltac:(solve [find_in])) as (WQD & AQD);
      pose proof (af_acc_live RT AF Σt3 mm tv 1024 A ltac:(solve [find_in])) as (WQT & AQT);
      pose proof (af_acc_live RT AF Σt3 mm t38 1024 A ltac:(solve [find_in])) as (WQ8 & AQ8) end.
    apply wr_at_rw_CB in WQB; [| clear - WPLO; lia]. destruct WQB as (lbs & QB). pose proof QB as [[[QBL _] _] _]. cbn in QBL. apply u8arr_of_rw_cells in QB.
    assert (QBL1 : Z.of_nat (length lbs) = p_wpl v * 4) by (rewrite QBL; clear - WPLO; lia). clear QBL.
    apply (wr_at_sub _ _ _ lined (4 * p_wpl v1)) in WQD; [| unfold lined; clear - HM0; lia | unfold lined; clear - HM0 HM1; lia | clear - WPLD1; lia].
    apply wr_at_rw_CB in WQD; [| clear - WPLD1; lia]. destruct WQD as (ljunk & QD). pose proof QD as [[[QDL _] _] _]. cbn in QDL. apply u8arr_of_rw_cells in QD.
    destruct (u8arr_u32arr _ lined ljunk (p_wpl v1) QD ltac:(rewrite QDL; clear - WPLD1; lia)) as (lwl & UQL & UQLL). clear QD QDL.
    assert (AQL : acc asegs _ lined (4 * p_wpl v1)) by (eapply acc_sub; [exact AQD| unfold lined; clear - HM0; lia | unfold lined; clear - HM0 HM1; lia]).
    apply wr_at_rw_CB in WQT; [| clear; lia]. destruct WQT as (tjunk & QT). pose proof QT as [[[QTL _] _] _]. cbn in QTL. apply u8arr_of_rw_cells in QT.
    destruct (u8arr_u32arr _ tv tjunk 256 QT ltac:(rewrite QTL; clear; lia)) as (ltw & UQT & UQTL). clear QT QTL.
    apply wr_at_rw_CB in WQ8; [| clear; lia]. destruct WQ8 as (t8junk & Q8). pose proof Q8 as [[[Q8L _] _] _]. cbn in Q8L. apply u8arr_of_rw_cells in Q8.
    destruct (u8arr_u32arr _ t38 t8junk 256 Q8 ltac:(rewrite Q8L; clear; lia)) as (lt8 & UQ8 & UQ8L). clear Q8 Q8L.
    pose proof FR as CBF. split_at CBF 12%nat CBF2. split_at CBF2 1%nat CBF3. clear CBF CBF3.
    lazymatch type of CBF2 with rw_cells _ _ ?A _ => replace A with (usp + -304 + 136) in CBF2 by (clear; lia) end.
    idtac "MARK B last-line premises".
    walk_to AF MST [(lined, lined + 4 * p_wpl v1); (bufs1, bufs1 + p_wpl v * 4)] [0x9eb14].
    eapply evt_cut.
    { lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        epose proof (d2l1_line _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -304) lined (4 * p_wpl v1) bufs1 bufs2 (p_wpl v * 4) tv t38 t14 (p_w v) lbs lwl ltw lt8
                       GEO1 MIx QB QBL1 ltac:(assumption) UQL ltac:(rewrite UQLL; clear; lia) AQL UQT UQTL ltac:(assumption) UQ8 UQ8L ltac:(assumption) CBF2
                       ltac:(clear - LOR STa; lia) ltac:(clear - SPT; lia) ltac:(unfold lined; clear - CKR2 LOW LOR HM0 HM1; lia) ltac:(clear - CKR3 LOW LOR; lia)) as ZR end.
      unfold SHB in ZR. exact ZR. }
    idtac "MARK B last line applied".
    clear QB UQL AQL UQT UQ8 CBF2.
    intros ms' PO. unfold d2l1_end in PO.
    destruct PO as (qt0 & qt1 & qt2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & qt3 & qt4 & qt5 & mE & lbs2 & lwl2 & -> & MUl & WMl & MIl & UB' & UBL' & ACCB' & UL' & ULL' & ACCL' & UT' & ACCT' & U38' & ACC38').
    clear UB' UBL' UL' ULL' UT' U38'.
    idtac "MARK B last line post".
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT.
    loop_art RT AF Σt3 mE lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [solve [find_in]| unfold lined in Hzz; clear - Hzz HM0 HM1; lia]| split; [intros zz Hzz; right; right; left; exists bufs1, (p_wpl v * 4); split; [solve [find_in]| clear - Hzz; lia]| exact I]]).
    lazymatch type of MUl with munch _ ?ma ?mb =>
      loop_transport ma mb MUl ltac:(fun Hx => clear - Hx CKR2 CKR3 CKS2 CKS3 LOW LOR STa SP0R0 HM0 HM1 WPLD1 WPLO; unfold parked in *; unfold lined; first [lia | Z.div_mod_to_equations; lia]) end.
    idtac "MARK B last line transported".
    carry_mu MUl FRM ltac:(fun Hx => repeat match goal with Hf : parked (fr + 256 <= ?b \/ _ <= fr) |- _ => unfold parked in Hf; revert Hf end; unfold lined; clear - Hx HM0 HM1; intros; repeat split; try exact I; lia).
    carry_mu MUl FSH ltac:(fun Hx => repeat match goal with Hf : parked (?b + _ <= fr / 8 + 2147450880 \/ (fr + 256) / 8 + 2147450880 <= ?b) |- _ => unfold parked in Hf; revert Hf end;
                             unfold shad, SHB in *; unfold lined; clear - Hx FR64 HM0 HM1; intros; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    carry_mu MUl PXD ltac:(fun Hx => unfold parked in DPD, A_pdb1; unfold lined; clear - Hx DPD A_pdb1 HM0 HM1; repeat split; try exact I; lia).
    carry_mu MUl PXS ltac:(fun Hx => unfold parked in DSD, A_pxb1; unfold lined; clear - Hx DSD A_pxb1 HM0 HM1; repeat split; try exact I; lia).
    carry_mu MUl PXT ltac:(fun Hx => unfold parked in A_datt, A_ttb1; unfold lined; clear - Hx A_datt A_ttb1 HM0 HM1; repeat split; try exact I; lia).
    idtac "MARK B last line carried".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [solve [find_in]| unfold lined in Hzz; clear - Hzz HM0 HM1; lia]| split; [intros zz Hzz; right; right; left; exists bufs1, (p_wpl v * 4); split; [solve [find_in]| clear - Hzz; lia]| exact I]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx =>
      pose proof (NCD _ Hx) as Y1; pose proof (NCB1 _ Hx) as Y2; cbn [outside]; unfold lined; clear - Y1 Y2 HM0 HM1; repeat split; try exact I; lia) end.
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK B after last line".
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixcmapCreateLinear; 0x9ed54].
    idtac "MARK arm B at cmaplin".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK B at_call CML".
    eapply cps_seq.
    { eapply CML with (lo := lo).
      - exact FDO.
      - exact MST.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lenv_tac.
      - unfold lres; rewrite FRSt3, LVT3; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split;
        [ clear - FRB; lia | clear - LVB; lia | clear - CRt3 CRB; unfold RASTER_COST in *; lia
        | intros p9 n9 Hp; cbn [In] in Hp; repeat (destruct Hp as [Hp|Hp]; [apply (f_equal snd) in Hp; cbn [snd] in Hp; rewrite <- Hp; first [exact DDN | exact DTN | clear - WPLO; lia | clear; lia] |]); exact (LVP p9 n9 Hp) ]. }
    idtac "MARK B CML applied".
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT.
    after_call RT AF.
    idtac "MARK B after_call CML".
    lazymatch goal with A : ART RT ?S ?mm, C : cmap_obj (rt_live RT ?S) ?mm ?cm (mkCmapv ?ca 2 4 4) |- cps _ (ASTA RT ?S _ _) _ =>
      rename S into Σm; rename A into ARTM; rename cm into cmap; rename ca into carr; rename C into CMO end.
    lazymatch goal with H : rt_live RT Σm = _ |- _ => rename H into LVMN end.
    lazymatch goal with H : rw_cells asegs _ carr cmaplin24_cells |- _ => rename H into CAR end.
    assert (LVM : rt_live RT Σm = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVMN, LVT3; reflexivity).
    assert (FRSm : rt_frames RT Σm = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σm = _ |- _ => rewrite E end; exact FRSt3).
    assert (SP0m : rt_sp0 RT Σm = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRm : rt_credit RT Σ - (2 * RASTER_COST + 25) <= rt_credit RT Σm) by (lazymatch goal with E : rt_credit RT Σt3 <= rt_credit RT Σm |- _ => clear - E CRt3; lia end).
    assert (LSUBm : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σm)) by (intros e He; rewrite LVM; solve [find_in]).
    pose proof CMO as ((cpad & CMC) & (CQIN & CQ0 & CQ16 & _) & (KAIN & KA0 & KA16 & _) & COK & CANE). cbn [c_arr c_depth c_nalloc c_n] in KAIN, KA0, KA16, CANE.
    change (4 * 4) with 16 in KAIN.
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK B carried CML".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => exact I).
    (* [comment removed for export] *)
    assert (NECM : forall e, In e ((t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> cmap)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σm _ [(carr, 16)] cmap 24 _ e ARTM LVM); [cbn [app]; right; exact He| clear; lia| exact Hn]).
    assert (NECA : forall e, In e ((cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> 0 < snd e -> fst e <> carr)
      by (intros e He Hn; apply (fresh_chunk_ne RT AF Σm _ [] carr 16 _ e ARTM LVM); [cbn [app]; exact He| clear; lia| exact Hn]).
    assert (SUBCM : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σm) /\ fst e <> cmap)
      by (intros e He; split; [exact (LSUBm e He)| apply NECM; [solve [find_in]| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (SUBCA : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σm) /\ fst e <> carr)
      by (intros e He; split; [exact (LSUBm e He)| apply NECA; [solve [find_in]| destruct e as [eq ek]; exact (LVP eq ek He)]]).
    assert (NCCM : forall a, PF a -> a < cmap \/ cmap + 24 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σm _ cmap 24 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTM ltac:(rewrite LVM; right; left; reflexivity) SUBCM);
          [ rewrite FRSm; intros e He; right; exact He | rewrite SP0m; ul | exact (proj1 Ha) ]).
    assert (NCCA : forall a, PF a -> a < carr \/ carr + 16 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σm _ carr 16 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTM ltac:(rewrite LVM; left; reflexivity) SUBCA);
          [ rewrite FRSm; intros e He; right; exact He | rewrite SP0m; ul | exact (proj1 Ha) ]).
    assert (N_cmpd : cmap <> pixd) by (intros E; exact (NECM (pixd, 64) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_capd : carr <> pixd) by (intros E; exact (NECA (pixd, 64) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cmda : cmap <> dat) by (intros E; exact (NECM (dat, rs) ltac:(solve [find_in]) DDN (eq_sym E))).
    assert (N_cada : carr <> dat) by (intros E; exact (NECA (dat, rs) ltac:(solve [find_in]) DDN (eq_sym E))).
    assert (N_cmpx : cmap <> pix) by (intros E; exact (NECM (pix, 64) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_capx : carr <> pix) by (intros E; exact (NECA (pix, 64) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cmsd : cmap <> p_data v) by (intros E; exact (NECM (p_data v, 4 * (p_wpl v * p_h v)) ltac:(solve [find_in]) DSZ (eq_sym E))).
    assert (N_casd : carr <> p_data v) by (intros E; exact (NECA (p_data v, 4 * (p_wpl v * p_h v)) ltac:(solve [find_in]) DSZ (eq_sym E))).
    assert (N_cmb1 : cmap <> bufs1) by (intros E; exact (NECM (bufs1, p_wpl v * 4) ltac:(solve [find_in]) ltac:(cbn; clear - WPLO; lia) (eq_sym E))).
    assert (N_cab1 : carr <> bufs1) by (intros E; exact (NECA (bufs1, p_wpl v * 4) ltac:(solve [find_in]) ltac:(cbn; clear - WPLO; lia) (eq_sym E))).
    assert (N_cmb2 : cmap <> bufs2) by (intros E; exact (NECM (bufs2, p_wpl v * 4) ltac:(solve [find_in]) ltac:(cbn; clear - WPLO; lia) (eq_sym E))).
    assert (N_cab2 : carr <> bufs2) by (intros E; exact (NECA (bufs2, p_wpl v * 4) ltac:(solve [find_in]) ltac:(cbn; clear - WPLO; lia) (eq_sym E))).
    assert (N_cmtv : cmap <> tv) by (intros E; exact (NECM (tv, 1024) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_catv : carr <> tv) by (intros E; exact (NECA (tv, 1024) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cmt38 : cmap <> t38) by (intros E; exact (NECM (t38, 1024) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cat38 : carr <> t38) by (intros E; exact (NECA (t38, 1024) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cmtt : cmap <> pixt) by (intros E; exact (NECM (pixt, 64) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_catt : carr <> pixt) by (intros E; exact (NECA (pixt, 64) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cmdt : cmap <> dtt) by (intros E; exact (NECM (dtt, rst) ltac:(solve [find_in]) DTN (eq_sym E))).
    assert (N_cadt : carr <> dtt) by (intros E; exact (NECA (dtt, rst) ltac:(solve [find_in]) DTN (eq_sym E))).
    assert (N_cmt14 : cmap <> t14) by (intros E; exact (NECM (t14, 1024) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    assert (N_cat14 : carr <> t14) by (intros E; exact (NECA (t14, 1024) ltac:(solve [find_in]) ltac:(cbn; clear; lia) (eq_sym E))).
    lazymatch goal with A : ART RT Σm ?mm |- _ =>
      pose proof (live_apart2 RT AF Σm mm pixd 64 cmap 24 A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_cmpd (eq_sym (f_equal fst E))))) as A_pdcm;
      pose proof (live_apart2 RT AF Σm mm pixd 64 carr 16 A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_capd (eq_sym (f_equal fst E))))) as A_pdca;
      pose proof (live_apart2 RT AF Σm mm pix 64 cmap 24 A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_cmpx (eq_sym (f_equal fst E))))) as A_pxcm;
      pose proof (live_apart2 RT AF Σm mm pix 64 carr 16 A ltac:(solve [find_in]) ltac:(solve [find_in]) ltac:(intros E; exact (N_capx (eq_sym (f_equal fst E))))) as A_pxca end.
    park A_pdcm. park A_pdca. park A_pxcm. park A_pxca.
    chunk_facts RT AF GP cmap 24. chunk_facts RT AF GP carr 16.
    fframe_chunk RT AF fr 2%nat 256 cmap 24. fframe_chunk RT AF fr 2%nat 256 carr 16.
    idtac "MARK B CML facts".
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixSetColormap; 0x9ed54].
    idtac "MARK arm B at pixSetColormap".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK B at_call PSC".
    set (vf := pv_inf (pv_res v1 v) v).
    unfold hid in HOKD.
    lazymatch goal with PX : rw_cells asegs ?mc pixd _ |- cps _ (ASTA RT Σm _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (PODm : pix_obj (rt_live RT Σm) mc pixd vf (mkCmapv carr 2 4 4))
        by (split; [unfold pix_cells, vf, pv_inf, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP; exact PX|];
            split; [split; [solve [find_in]| split; [exact PD0| split; [exact PD16| clear; lia]]]|];
            split; [exact HOKD|];
            split; [right; split; [split; [solve [find_in]| split; [exact DD0| split; [exact DD16| exact DDN]]]| unfold parked in DDNE; exact DDNE]| left; exact VCMAP]);
      assert (CMOm : cmap_obj (rt_live RT Σm) mc cmap (mkCmapv carr 2 4 4))
        by (split; [exists cpad; exact CMC| split; [split; [solve [find_in]| split; [exact CQ0| split; [exact CQ16| clear; lia]]]| split; [split; [cbn [c_arr c_nalloc]; solve [find_in]| split; [exact KA0| split; [exact KA16| cbn; clear; lia]]]| split; [exact COK| exact CANE]]]]) end.
    hide HOKD.
    idtac "MARK B PSC objs".
    eapply cps_seq.
    { eapply PSC with (lo := lo) (pix := pixd) (cmap := cmap) (v := vf) (cv := mkCmapv carr 2 4 4).
      - exact FDO.
      - exact MST.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact PODm.
      - exact VCMAP.
      - exact VDATA1.
      - exact CMOm.
      - exact N_cmpd.
      - cbn [c_arr]. exact N_capd.
      - exact N_cmda.
      - cbn [c_arr]. exact N_cada.
      - lenv_tac.
      - unfold lres; rewrite FRSm, LVM; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split;
        [ clear - FRB; lia | clear - LVB; lia | clear - CRm CRB; unfold RASTER_COST in *; lia
        | intros p9 n9 Hp; cbn [In] in Hp; repeat (destruct Hp as [Hp|Hp]; [apply (f_equal snd) in Hp; cbn [snd] in Hp; rewrite <- Hp; first [exact DDN | exact DTN | clear - WPLO; lia | clear; lia] |]); exact (LVP p9 n9 Hp) ]. }
    idtac "MARK B PSC applied".
    clear PODm CMOm.
    hide FRM. hide FSH. hide PXS. hide PXT. hide CAR. hide CMC. clear PXD.
    after_call RT AF.
    idtac "MARK B after_call PSC".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σs; rename A into ARTS end.
    lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
    unfold pix_cells, vf, pv_inf, pv_res in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD in PXD. fold dat in PXD.
    assert (LVS : rt_live RT Σs = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (bufs1, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σs = _ |- _ => rewrite E end; exact LVM).
    assert (FRSs : rt_frames RT Σs = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σs = _ |- _ => rewrite E end; exact FRSm).
    assert (SP0s : rt_sp0 RT Σs = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRs : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σs) by (lazymatch goal with E : rt_credit RT Σm - 6 <= rt_credit RT Σs |- _ => clear - E CRm; lia end).
    assert (LSUBs : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σs)) by (intros e He; rewrite LVS; solve [find_in]).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => repeat match goal with Hf : parked (fr + 256 <= pixd \/ _ <= fr) |- _ => unfold parked in Hf; revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => repeat match goal with Hf : parked (pixd + _ <= fr / 8 + 2147450880 \/ (fr + 256) / 8 + 2147450880 <= pixd) |- _ => unfold parked in Hf; revert Hf end; unfold shad, SHB in *; clear - Hx FR64; intros; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in DSP; clear - Hx DSP; repeat split; try exact I; lia);
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in DPXT; clear - Hx DPXT; repeat split; try exact I; lia);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| unfold cmaplin24_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; exact Hx]) ltac:(fun Hx => unfold parked in A_pdca; unfold cmaplin24_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; clear - Hx A_pdca; repeat split; try exact I; lia);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| unfold cmap_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; exact Hx]) ltac:(fun Hx => unfold parked in A_pdcm; unfold cmap_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; clear - Hx A_pdcm; repeat split; try exact I; lia) end.
    idtac "MARK B carried PSC".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; pose proof (NCP _ (conj Hx1 Hx2)) as Y; clear - Y; repeat split; try exact I; lia).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    idtac "MARK B after PSC".
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9e494].
    idtac "MARK arm B at free 1".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    unfold cmaplin24_cells in CAR. unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC.
    assert (NRB1 : forall e, In e ((dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> bufs1)
      by (intros e He; apply (NEB1 e He); destruct He as [<-|[<-|[<-|[<-|He]]]]; [exact DTN| cbn; clear; lia| exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (NRB2 : forall e, In e ((dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> bufs2)
      by (intros e He; apply (NEB2 e); [right; exact He|]; destruct He as [<-|[<-|[<-|[<-|He]]]]; [exact DTN| cbn; clear; lia| exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (NRT1 : forall e, In e ((dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> tv)
      by (intros e He; apply (NET1 e); [do 2 right; exact He|]; destruct He as [<-|[<-|[<-|[<-|He]]]]; [exact DTN| cbn; clear; lia| exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (NRT2 : forall e, In e ((dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> t38)
      by (intros e He; apply (NET2 e); [do 3 right; exact He|]; destruct He as [<-|[<-|[<-|[<-|He]]]]; [exact DTN| cbn; clear; lia| exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (NRT3 : forall e, In e ((dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> t14)
      by (intros e He; apply (NET3 e); [do 4 right; exact He|]; destruct He as [<-|[<-|[<-|[<-|He]]]]; [exact DTN| cbn; clear; lia| exact DDN| cbn; clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    park_ne.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK B at_call free 1".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf1 : In (0x9ed5c :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := bufs1) (n := p_wpl v * 4); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVS; do 6 right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf1]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK B free 1 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf1; rename A into ARTF1 end.
    assert (LVF1 : rt_live RT Σf1 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, p_wpl v * 4) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf1 = _ |- _ => rewrite E end; rewrite LVS; rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cab1); rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmb1); rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b1t14)); rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b1t38)); rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b1tv)); rewrite (live_remove_cons' bufs1); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b1b2)); rewrite (live_remove_hd bufs1 _ _ NRB1); reflexivity).
    assert (FRSf1 : rt_frames RT Σf1 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf1 = _ |- _ => rewrite E end; assumption).
    assert (SP0f1 : rt_sp0 RT Σf1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf1 : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σf1) by (repeat match goal with E : rt_credit RT Σf1 = _ |- _ => rewrite E end; exact CRs).
    assert (LSUBf1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf1)) by (intros e He; rewrite LVF1; repeat right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK B carried f1".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf1| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9e494].
    idtac "MARK arm B after free 1".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK B at_call free 2".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf2 : In (0x9ed64 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := bufs2) (n := p_wpl v * 4); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVF1; do 5 right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf2]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK B free 2 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf2; rename A into ARTF2 end.
    assert (LVF2 : rt_live RT Σf2 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf2 = _ |- _ => rewrite E end; rewrite LVF1; rewrite (live_remove_cons' bufs2); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cab2); rewrite (live_remove_cons' bufs2); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmb2); rewrite (live_remove_cons' bufs2); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b2t14)); rewrite (live_remove_cons' bufs2); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b2t38)); rewrite (live_remove_cons' bufs2); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_b2tv)); rewrite (live_remove_hd bufs2 _ _ NRB2); reflexivity).
    assert (FRSf2 : rt_frames RT Σf2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf2 = _ |- _ => rewrite E end; assumption).
    assert (SP0f2 : rt_sp0 RT Σf2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf2 : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σf2) by (repeat match goal with E : rt_credit RT Σf2 = _ |- _ => rewrite E end; exact CRf1).
    assert (LSUBf2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf2)) by (intros e He; rewrite LVF2; repeat right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK B carried f2".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf2| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9e494].
    idtac "MARK arm B after free 2".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK B at_call free 3".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf3 : In (0x9ed6c :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := tv) (n := 1024); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVF2; do 4 right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf3]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK B free 3 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf3; rename A into ARTF3 end.
    assert (LVF3 : rt_live RT Σf3 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf3 = _ |- _ => rewrite E end; rewrite LVF2; rewrite (live_remove_cons' tv); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_catv); rewrite (live_remove_cons' tv); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmtv); rewrite (live_remove_cons' tv); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_tvt14)); rewrite (live_remove_cons' tv); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_tvt38)); rewrite (live_remove_hd tv _ _ NRT1); reflexivity).
    assert (FRSf3 : rt_frames RT Σf3 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf3 = _ |- _ => rewrite E end; assumption).
    assert (SP0f3 : rt_sp0 RT Σf3 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf3 : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σf3) by (repeat match goal with E : rt_credit RT Σf3 = _ |- _ => rewrite E end; exact CRf2).
    assert (LSUBf3 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf3)) by (intros e He; rewrite LVF3; repeat right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK B carried f3".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf3| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9e494].
    idtac "MARK arm B after free 3".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK B at_call free 4".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf4 : In (0x9ed74 :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := t38) (n := 1024); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVF3; do 3 right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf4]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK B free 4 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf4; rename A into ARTF4 end.
    assert (LVF4 : rt_live RT Σf4 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf4 = _ |- _ => rewrite E end; rewrite LVF3; rewrite (live_remove_cons' t38); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cat38); rewrite (live_remove_cons' t38); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmt38); rewrite (live_remove_cons' t38); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym N_t38t14)); rewrite (live_remove_hd t38 _ _ NRT2); reflexivity).
    assert (FRSf4 : rt_frames RT Σf4 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf4 = _ |- _ => rewrite E end; assumption).
    assert (SP0f4 : rt_sp0 RT Σf4 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf4 : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σf4) by (repeat match goal with E : rt_credit RT Σf4 = _ |- _ => rewrite E end; exact CRf3).
    assert (LSUBf4 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf4)) by (intros e He; rewrite LVF4; repeat right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK B carried f4".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf4| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free; 0x9e494].
    idtac "MARK arm B after free 4".
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK B at_call free 5".
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    assert (TRf5 : In (0x9ed7c :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; apply ct_mem_In; vm_compute; reflexivity).
    lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    clear FRrec2.
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := t14) (n := 1024); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => rewrite LVF4; do 2 right; left; reflexivity
           | |- unwind_okC _ _ _ _ => exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia); split; [exact UCC| exact TRf5]
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK B free 5 applied".
    clear UCC.
    hide FRM. hide FSH. hide PXD. hide PXS. hide PXT. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf5; rename A into ARTF5 end.
    assert (LVF5 : rt_live RT Σf5 = (carr, 16) :: (cmap, 24) :: (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
      by (repeat match goal with E : rt_live RT Σf5 = _ |- _ => rewrite E end; rewrite LVF4; rewrite (live_remove_cons' t14); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cat14); rewrite (live_remove_cons' t14); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmt14); rewrite (live_remove_hd t14 _ _ NRT3); reflexivity).
    assert (FRSf5 : rt_frames RT Σf5 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf5 = _ |- _ => rewrite E end; assumption).
    assert (SP0f5 : rt_sp0 RT Σf5 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf5 : rt_credit RT Σ - (2 * RASTER_COST + 31) <= rt_credit RT Σf5) by (repeat match goal with E : rt_credit RT Σf5 = _ |- _ => rewrite E end; exact CRf4).
    assert (LSUBf5 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf5)) by (intros e He; rewrite LVF5; repeat right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia]) ltac:(fun Hx => exact I);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx PXT ltac:(fun x Hx => right; right; left; exists pixt, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => exact I) end.
    idtac "MARK B carried f5".
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [exact LSUBf5| solve [frames_sub_tac]| clear; lia]).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDestroy; 0x9e494].
    idtac "MARK arm B after free 5".
  (* [comment removed for export] *)
    (* [comment removed for export] *)
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => agf_side PFS NFA LOR Hx).
    idtac "MARK B at_call DES".
    (* [comment removed for export] *)
    split_at FRM 10%nat PPC. split_at PPC 1%nat FRMb.
    pose proof FSH as SH10. split_at SH10 10%nat SH10b. split_at SH10b 1%nat SH10c. clear SH10 SH10c.
    lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval lazy in (Nat.sub (length cs) 2) in pose proof FR as FRrec; split_at FRrec n FRrec2; clear FRrec end.
    unfold hid in HOKT.
    lazymatch goal with PT : rw_cells asegs ?mc pixt _ |- cps _ (ASTA RT Σf5 _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (POT4 : pix_obj (rt_live RT Σf5) mc pixt vt (mkCmapv 0 0 0 0))
        by (split; [unfold pix_cells; rewrite WT, HT, DT, CMT, EWT; exact PT|]; split; [split; [solve [find_in]| split; [exact PT0| split; [exact PT16| clear; lia]]]|];
            split; [exact HOKT|]; split; [right; split; [split; [solve [find_in]| split; [exact DT0| split; [exact DT16| exact DTN]]]| unfold parked in DTNE; exact DTNE]| left; exact CMT]);
      assert (OPP : optrL RT (live_destroy pixt vt (mkCmapv 0 0 0 0) (rt_live RT Σf5)) Σf5 mc (fr + 80) 8)
        by (unfold optrL, accok; split;
            [ right; exists fr, 2%nat; rewrite FRSf5; change (fs_size 2) with 256;
              split; [left; reflexivity|]; split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FR0; lia|];
              split; [clear - FRHI SP0R1; lia|];
              replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
              destruct SH10b as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B
            | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; unfold SEGTOP_A; split; [clear - FRSH; unfold parked in FRSH; lia| clear - FRSEG; unfold parked in FRSEG; lia] ]);
      assert (UCC : chain_ok mc (usp + -304) usp (bv_unsigned ra :: ras))
        by (apply (chain_ok_push _ (usp + -304) usp (bv_unsigned ra) (bv_unsigned s0) ras);
              [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | rewrite RAF; unfold RA_FUZZ_OP1; clear; lia
              | let RSx := fresh "RSx" in pose proof (bv_unsigned_in_range 64 s0) as RSx; unfold bv_modulus in RSx; change (2 ^ Z.of_N 64) with (2^64) in RSx; exact RSx
              | rewrite !Z_to_bv_bv_unsigned; lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end
              | apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; unfold PF; cbn [outside];
                split; [left; exact Hzx| split; [clear - Hzx CKR LOW LOR; lia| exact I]] ]) end.
    hide HOKT. clear FRrec2.
    idtac "MARK B destroy args".
    assert (CR1 : 1 <= rt_credit RT Σf5) by (clear - CRf5 CRB; unfold RASTER_COST in *; lia).
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
    - rewrite RAF, RAS. unfold DESTROY_FREE_RAS, RA_FUZZ_OP1, RA_TOP. rewrite unsigned_lit by (clear; lia).
      repeat (apply Forall_cons; [apply ct_mem_In; vm_compute; reflexivity |]). apply Forall_nil.
    - lenv_tac.
    - unfold lres; rewrite FRSf5, LVF5; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [clear - FRB; lia| clear - LVB; lia| exact CR1|
        intros p9 n9 Hp; cbn [In] in Hp; repeat (destruct Hp as [Hp|Hp]; [apply (f_equal snd) in Hp; cbn [snd] in Hp; rewrite <- Hp; first [exact DDN | exact DTN | clear - WPLO; lia | clear; lia] |]); exact (LVP p9 n9 Hp)].
    }
    idtac "MARK B DES applied".
    clear POT4 OPP UCC CR1 SH10b. lazymatch goal with PT : rw_cells asegs _ pixt _ |- _ => clear PT end.
    hide FRM. hide FRMb. hide FSH. hide PXD. hide PXS. hide CAR. hide CMC.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σz; rename A into ARTZ end.
    (* [comment removed for export] *)
    unfold hid in SUBT, SUBDT.
    assert (FRDT : forall e, In e ((pixt, 64) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> dtt)
      by (intros e [<-|He]; [cbn [fst]; unfold parked in DTNE; exact (not_eq_sym DTNE)| exact (proj2 (SUBDT e He))]).
    assert (FRTT : forall e, In e ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) -> fst e <> pixt) by (intros e He; exact (proj2 (SUBT e He))).
    hide SUBT. hide SUBDT.
    assert (LVZ : rt_live RT Σz = (carr, 16) :: (cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ).
    { repeat match goal with E : rt_live RT Σz = _ |- _ => rewrite E end. rewrite LVF5.
      unfold live_destroy, rm_opt. rewrite CMT. cbn [Z.eqb]. change (p_data vt) with dtt.
      unpark DATAT. rewrite (proj2 (Z.eqb_neq _ _) DATAT).
      rewrite (live_remove_cons' dtt); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cadt).
      rewrite (live_remove_cons' dtt); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmdt).
      rewrite (live_remove_hd dtt _ _ FRDT).
      rewrite (live_remove_cons' pixt); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_catt).
      rewrite (live_remove_cons' pixt); cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) N_cmtt).
      rewrite (live_remove_hd pixt _ _ FRTT). reflexivity. }
    clear FRDT FRTT.
    assert (FRSz : rt_frames RT Σz = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σz = _ |- _ => rewrite E end; exact FRSf5).
    assert (SP0z : rt_sp0 RT Σz = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRz : rt_credit RT Σ - (2 * RASTER_COST + 32) <= rt_credit RT Σz) by (lazymatch goal with E : rt_credit RT Σf5 - 1 <= rt_credit RT Σz |- _ => clear - E CRf5; lia end).
    assert (LSUBz : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σz)) by (intros e He; rewrite LVZ; do 4 right; exact He).
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => unfold parked in FCD; clear - Hx FCD; lia);
      carry AGx FRMb ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => unfold parked in FCD; clear - Hx FCD; lia);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia])
                    ltac:(fun Hx => unfold parked in FCS, FRSH; unfold shad, SHB in *; clear - Hx FCS FR64 FRSH CKH; first [lia | Z.div_mod_to_equations; lia]);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in FCD1, DSP; clear - Hx FCD1 DSP; lia);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => unfold parked in FCD; clear - Hx FCD; lia);
      carry AGx CAR ltac:(fun x Hx => right; right; left; exists carr, 16; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => cside carr Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0);
      carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [solve [find_in]| exact Hx]) ltac:(fun Hx => cside cmap Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0) end.
    idtac "MARK B carried z".
    fold_pres2 usp ltac:(fun Hx1 Hx2 => cbn [outside]; cbn [outside] in Hx2; destruct (NFA _ (conj Hx1 Hx2)) as [N1 N2]; clear - N1 Hx2; repeat split; try exact I; lia).
    clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    (* [comment removed for export] *)
    unfold hid in SUBP, SUBD.
    assert (SUBP' : forall e, In e (rt_live RT Σ) -> fst e <> pixd) by (intros e He; exact (proj2 (SUBP e He))).
    assert (SUBD' : forall e, In e (rt_live RT Σ) -> fst e <> dat) by (intros e He; exact (proj2 (SUBD e He))).
    clear SUBP SUBD.
    assert (PDINz : In (pixd, 64) (rt_live RT Σz)) by (rewrite LVZ; do 3 right; left; reflexivity).
    assert (DDINz : In (dat, rs) (rt_live RT Σz)) by (rewrite LVZ; do 2 right; left; reflexivity).
    assert (PINz : In (pix, 64) (rt_live RT Σz)) by (rewrite LVZ; do 4 right; exact PIN).
    assert (DINz : In (p_data v, 4 * (p_wpl v * p_h v)) (rt_live RT Σz)) by (rewrite LVZ; do 4 right; exact DIN).
    assert (CMINz : In (cmap, 24) (rt_live RT Σz)) by (rewrite LVZ; right; left; reflexivity).
    assert (CAINz : In (carr, 16) (rt_live RT Σz)) by (rewrite LVZ; left; reflexivity).
    unfold hid in SUBCM, SUBCA.
    assert (SUBCM' : forall e, In e (rt_live RT Σ) -> fst e <> cmap) by (intros e He; exact (proj2 (SUBCM e He))).
    assert (SUBCA' : forall e, In e (rt_live RT Σ) -> fst e <> carr) by (intros e He; exact (proj2 (SUBCA e He))).
    clear SUBCM SUBCA.
    sigma_gc RT Σ Σz.
    repeat match goal with H : In (?b, _) (rt_live RT Σ) |- _ => lazymatch b with pix => fail | p_data v => fail | _ => clear H end end.
    idtac "MARK B diet".
    try forget_junk FR; try forget_junk FRM; try forget_junk FSH; try forget_junk FRMb.
    hide PXS. hide PXD. hide CAR. hide CMC.
    (* [comment removed for export] *)
    split_at FR 5%nat FRD. split_at FRD 10%nat FRT.
    lazymatch type of FRD with rw_cells _ ?mq ?A ?cs => destruct (rw_cells_forget asegs mq A cs FRD) as [jdead FRD']; clear FRD; cbn [cells_size csize Nat.add] in FRD' end.
    join_cells FR FRD'. join_cells FR FRT.
    repeat match goal with H : context [bufs1] |- _ => clear H end.
    repeat match goal with H : context [bufs2] |- _ => clear H end.
    repeat match goal with H : context [tv] |- _ => clear H end.
    repeat match goal with H : context [t38] |- _ => clear H end.
    repeat match goal with H : context [t14] |- _ => clear H end.
    repeat match goal with H : context [lined] |- _ => clear H end.
    repeat match goal with H : context [pixt] |- _ => clear H end.
    repeat match goal with H : context [dtt] |- _ => clear H end.
    repeat match goal with H : context [rst] |- _ => clear H end.
    repeat match goal with H : context [vt] |- _ => clear H end.
    clear lined. try clear rst. try clear dtt. try clear bufs1. try clear bufs2. try clear tv. try clear t38. try clear t14. try clear pixt. try clear vt.
    repeat match goal with H : wmono _ _ ?b |- _ => lazymatch goal with |- context [b] => fail | _ => clear H end end.
    repeat match goal with H : munch _ _ ?b |- _ => lazymatch goal with |- context [b] => fail | _ => clear H end end.
    idtac "MARK B diet 2".
    (* [comment removed for export] *)
    clear_acc.
    hide FCD. hide FCS. hide CKH. hide FCD1. hide FCS1. hide CKH1. hide DDNE. hide CANE. hide N_cmpd. hide N_cmda. hide N_capd. hide N_cada. hide VDATA1. hide FRSH.
    repeat match goal with H : parked ?T |- _ =>
      lazymatch T with context [fr] => lazymatch T with context [cmap] => hide H | context [carr] => hide H | _ => clear H end | _ => clear H end end.
    unfold hid in FRSH. unpark FRSH.
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 368, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9e4f0].
    idtac "MARK B at flag load".
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    idtac "MARK B at pokes".
    try unfold hid in FRM. try unfold hid in FSH. split_at FRM 1%nat FRMr.
    Time (eapply evt_cut;
    [ eapply EVQ_exit;
      [ eapply d2bpp_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
      | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
    | ]).
    clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold d2bpp_exit_W, SHB in MUx. unfold d2bpp_sh_f5 in FSH.
    idtac "MARK B pokes applied".
    Time loop_art RT AF Σz mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    Time (lazymatch type of MUx with munch _ ?ma ?mb =>
      loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *; clear - Hx FRHI FRSH FRSEG LOW LOR FR64 FR0 SP0R1 SP0R0 SP0W; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end).
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => unfold parked in FCD, CKH, FRSH; unfold shad, SHB in *; clear - Hx FCD CKH FRSH FRHI SP0R0 SP0R1 CKR LOW LOR FR64 FR0; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
      carry_mu MUx PXD ltac:(fun Hx => unfold parked in FCD1, CKH1, FRSH; unfold shad, SHB in *; clear - Hx FCD1 CKH1 FRSH FRHI SP0R0 SP0R1 CKR1 LOW LOR FR64 FR0; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
      carry_mu MUx CAR ltac:(fun Hx => cside carr Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0);
      carry_mu MUx CMC ltac:(fun Hx => cside cmap Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0) end.
    hide PXS. hide PXD. hide CAR. hide CMC.
    repeat match goal with H : parked _ |- _ => hide H end.
    join_cells FRM FRMr.
    idtac "MARK B carried x".
    frame_release_g RT AF GP MST Σ fr 2%nat 256 PF AGF PFS usp lo 0x9e5a4
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => agf_side PFS NFA LOR Hx) ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
    idtac "MARK B frame released".
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    lazymatch goal with MUx : munch [(?fl, ?fl + 1)] _ ?mb |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => repeat match goal with Hf : fl < pix \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx PXD ltac:(fun Hx => repeat match goal with Hf : fl < pixd \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx CAR ltac:(fun Hx => repeat match goal with Hf : fl < carr \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia);
      carry_mu MUx CMC ltac:(fun Hx => repeat match goal with Hf : fl < cmap \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; repeat split; try exact I; lia) end.
    hide PXS. hide PXD. hide CAR. hide CMC.
    clear_acc. refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    walk_to AF MST [(usp - 368, usp)] [0x9e5fc].
    (* [comment removed for export] *)
    try change (Z_to_bv 64 (bv_unsigned sp + -288)) with (Z_to_bv 64 (usp + -288)).
    awalk (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -304) |- _ => release_frame FR ST' usp end.
    lazymatch goal with MUx : munch _ _ ?mb |- evt _ _ (MS _ _ _ _ _ ?mb _) =>
      carry_mu MUx PXS ltac:(fun Hx => clear - Hx CKR LOW LOR; repeat split; try exact I; lia);
      carry_mu MUx PXD ltac:(fun Hx => clear - Hx CKR1 LOW LOR; repeat split; try exact I; lia);
      carry_mu MUx CAR ltac:(fun Hx => cside carr Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0);
      carry_mu MUx CMC ltac:(fun Hx => cside cmap Hx FRHI SP0R0 SP0R1 LOW LOR FR64 FR0) end.
    cps_stop.
    idtac "MARK B epilogue walked".
    apply cps_finish; intros c Hc; subst QF; unfold d2bpp_post; cbv beta.
    set (vg := mkPixv (p_w vf) (p_h vf) (p_d vf) (p_spp vf) (p_wpl vf) (p_xres vf) (p_yres vf) (p_inf vf) (p_spec vf) cmap (p_data vf)).
    assert (VGC : p_cmap vg = cmap) by reflexivity.
    assert (VGD : p_data vg = dat) by reflexivity.
    assert (CMNZ : cmap <> 0) by (clear - CQ0; lia).
    unfold hid in HOKD, CAR, CMC.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, pixd, vg, (mkCmapv carr 2 4 4) end.
    split.
    2: {
    split; [intros Z0; exfalso; clear - Z0 PD0; lia|].
    split.
    { intros _. rewrite LV2, LVZ.
      assert (CA0' : carr <> 0) by (clear - KA0; lia).
      unfold parked in N_cmpd, N_cmda, N_capd, N_cada, CANE.
      pose proof (live_destroy_tmpl (rt_live RT Σ) pixd dat rs cmap carr 16 vg (mkCmapv carr 2 4 4) VGD VGC
                    (fun _ => eq_refl) VDATA1 ltac:(unfold parked in DDNE; exact DDNE)
                    (fun _ => conj CA0' (conj N_cmpd (conj N_cmda (conj N_capd (conj N_cada CANE)))))
                    (fun e He => conj (SUBP' e He) (SUBD' e He)) (fun _ e He => conj (SUBCM' e He) (SUBCA' e He))) as LD.
      rewrite (proj2 (Z.eqb_neq cmap 0) CMNZ) in LD. exact LD. }
    split.
    { intros p9 n9 Hp. rewrite LV2, LVZ in Hp. cbn [In] in Hp. repeat (destruct Hp as [Hp|Hp]; [injection Hp; intros En Ep; rewrite <- En; first [exact DDN | clear; lia] |]). exact (LVP p9 n9 Hp). }
    split; [rewrite LV2, LVZ; cbn [length]; clear; lia|].
    split; [exact FRS2|]. split; [rewrite SP2; exact SP0z|].
    unfold D2_COST, OP_COST, is_d8. cbn [Z.eqb Pos.eqb].
    rewrite CR2. clear - CRz. unfold RASTER_COST in *. lia.
    }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    split; [unfold lpost_f, rt_after_f; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); split; [split; [assumption| split; assumption]| split; assumption]|].
    split; [unfold keepsL, rt_pres_fp; rewrite ?unsigned_lit by (clear - USP0 USP1; lia); intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
    split.
    { rewrite LV2, LVZ. lazymatch goal with PS : rw_cells asegs ?mc pix _ |- pix_obj _ ?mc _ _ _ =>
        exact (PSRC ((carr, 16) :: (cmap, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) 1 mc ltac:(intros e He; do 4 right; exact He) AGF PS) end. }
    right. split; [| rewrite VGD; exact VDATA1].
    rewrite LV2, LVZ.
    split; [unfold pix_cells, vg, vf, pv_inf, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD; exact PXD|].
    split; [split; [do 3 right; left; reflexivity| split; [exact PD0| split; [exact PD16| clear; lia]]]|].
    split; [exact HOKD|].
    split; [right; split; [split; [do 2 right; left; reflexivity| split; [exact DD0| split; [exact DD16| exact DDN]]]| unfold parked in DDNE; exact DDNE]|].
    right. cbn [c_arr]. split; [| split; [exact N_cmpd| split; [exact N_capd| split; [rewrite VGD; exact N_cmda| rewrite VGD; exact N_cada]]]].
    split; [exists cpad; unfold cmap_cells; cbn [c_arr c_depth c_nalloc c_n]; exact CMC|].
    split; [split; [right; left; reflexivity| split; [exact CQ0| split; [exact CQ16| clear; lia]]]|].
    split; [split; [cbn [c_arr c_nalloc]; left; reflexivity| split; [exact KA0| split; [exact KA16| cbn; clear; lia]]]|].
    split; [exact COK| exact CANE].
  (* [comment removed for export] *)
Qed.
End D2C.
