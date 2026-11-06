(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_objkit Lept_chain Lept_gmax_defs Ed_iface Numa_kit Px_defs Px_defs2 Px_kit Px_bkit Px_row Px_prof_defs LeptB_guard LeptB_guard2 Ed_fpkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac guard_fix ::= try sx32_fix; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end; swrap_fix; po_fix; al_fix; try mulh_fix.

Section PROFC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GETPIX : pixGetPixel1_cps RT.
Hypothesis SCANOFF : pixGetLastOffPixelInRunR_cps RT.
Hypothesis SCANON : pixGetLastOnPixelInRunL_cps RT.
Hypothesis NUMAC : numaCreate_cps RT.
Hypothesis NADDF : numaAddNumber_fast_cps RT.

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
(* [comment removed for export] *)
Local Ltac in_live_eq Hb :=
  first [ exact Hb
        | revert Hb; repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; let H := fresh in intro H; exact H ].
(* [comment removed for export] *)
Local Ltac kl_of_munch KL live MUx fr A0 FRSx LOW LOR :=
  lazymatch type of A0 with ART _ ?S ?m0 =>
  lazymatch type of MUx with munch ?W ?ma ?mb =>
    assert (KL : keeps_live live ma mb)
      by (apply (keeps_live_of_munch live W ma mb MUx);
          let b := fresh "b" in let kk := fresh "kk" in let a := fresh "a" in let Hb := fresh "Hb" in let Ha := fresh "Ha" in
          intros b kk a Hb Ha;
          let X1 := fresh "X" in let X2 := fresh "X" in let X3 := fresh "X" in let X4 := fresh "X" in
          pose proof (chunk_vs_frame RT AF S m0 fr 1%nat b kk a A0 ltac:(rewrite FRSx; left; reflexivity) Hb Ha) as (X1 & X2 & X3 & X4);
          change (fs_size 1%nat) with 128 in X1, X2; unfold shad, SHB in X2;
          repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E in X3 end;
          revert X1 X2 X3 X4 LOW LOR; clear; unfold STACK_WIN; intros; cbn [outside];
          repeat split; try exact I; lia) end end.
Local Ltac kl_of_ag KL live AGx fr A0 FRSx LOW LOR :=
  lazymatch type of A0 with ART _ ?S ?m0 =>
  lazymatch type of AGx with agree_on _ ?ma ?mb =>
    assert (KL : keeps_live live ma mb)
      by (apply (keeps_live_of_agree live _ ma mb AGx);
          let b := fresh "b" in let kk := fresh "kk" in let a := fresh "a" in let Hb := fresh "Hb" in let Ha := fresh "Ha" in
          intros b kk a Hb Ha; cbv beta;
          let X1 := fresh "X" in let X2 := fresh "X" in let X3 := fresh "X" in let X4 := fresh "X" in
          pose proof (chunk_vs_frame RT AF S m0 fr 1%nat b kk a A0 ltac:(rewrite FRSx; left; reflexivity) Hb Ha) as (X1 & X2 & X3 & X4);
          change (fs_size 1%nat) with 128 in X1, X2; unfold shad, SHB in X2;
          repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E in X3 end;
          split; [ right; right; left; exists b, kk; split; [ in_live_eq Hb | lia ]
                 | revert X1 X2 X3 X4 LOW LOR; clear; unfold STACK_WIN; intros; cbn [outside]; repeat split; try exact I; lia ]) end end.
(* [comment removed for export] *)
Local Ltac lvsub :=
  first [ solve [live_sub_tac]
        | let e := fresh "e" in let He := fresh "He" in intros e He;
          repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in * end;
          cbn [In]; cbn [In] in He; tauto ].

(* [comment removed for export] *)
Local Ltac cells_upto cs n :=
  lazymatch n with
  | 0%Z => constr:(O)
  | _ => lazymatch cs with
         | ?c :: ?rest =>
             let sz := eval cbn [csize] in (csize c) in
             let n' := eval vm_compute in (n - Z.of_nat sz)%Z in
             let k := cells_upto rest n' in constr:(S k)
         end
  end.
Local Ltac split_off H n H2 :=
  lazymatch type of H with rw_cells _ _ _ ?cs => let k := cells_upto cs n in split_at H k H2 end.

Lemma profile_c0 : profile_case RT 0.
Proof using AF GP GETPIX SCANOFF SCANON NUMAC NADDF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    FDO MST -> -> -> -> POBJ D1 VDATA UC TR ENV RES AL.
  unfold lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  unfold PROFILE_COST in *.
  assert (MC0 : 0 <= mcost (4 * p_h v)) by (unfold mcost; destruct (_ <=? _); lia).
  assert (HWH : p_w v + 3 <= p_h v * (p_w v + 3)) by (clear - HW1 HH1; nia).
  assert (CRR : (p_h v - 1) * (p_w v + 3) = p_h v * (p_w v + 3) - p_w v - 3) by (clear; nia).
  set (hw2 := p_h v * (p_w v + 3)) in *. set (mch := mcost (4 * p_h v)) in *.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixGetEdgeProfile, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
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
  carve_frame 160%nat ST.
  walk_to AF MST [(usp - 160, usp)] [e_stack_malloc 1%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [lvsub]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
  fframe_chunk RT AF fr 1%nat 128 pix 64.
  fframe_chunk RT AF fr 1%nat 128 (p_data v) (4 * (p_wpl v * p_h v)).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 160, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x12ca1c].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH.
  park_disj.
  rewrite D1 in PXC.
  (* [comment removed for export] *)
  pwalk_to AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_numaCreate; e_stack_malloc 1%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  rewrite !(sx32_small (p_h v)) by lia.
  assert (RAV : 4096 <= bv_unsigned ra < 2^64) by (unfold numaCreate_trace_ok in TR; exact (Forall_inv TR)).
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRtop. clear FRrec.
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
  assert (UC1 : uctx mc (Z_to_bv 64 (usp + -160)) (Z_to_bv 64 usp) (bv_unsigned ra :: ras)) by
   (unfold uctx in UC |- *; rewrite !unsigned_lit by lia;
    apply (chain_ok_push mc (usp + -160) usp (bv_unsigned ra) (bv_unsigned s0) ras);
    [ lia | lia | unfold USTACK_TOP; lia
    | exact RAV
    | pose proof (bv_unsigned_in_range 64 s0); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | rewrite !Z_to_bv_bv_unsigned; exact FRtop
    | apply (chain_ok_keep ras m mc _ _ UC); intros aa Haa; apply AGF; subst PF; cbv beta; left; unfold usp in *; ul ]) end.
  eapply cps_seq.
  { eapply NUMAC with (lo := lo) (n := p_h v) (ras := bv_unsigned ra :: ras).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - split; [lia| reflexivity].
    - lia.
    - exact UC1.
    - exact TR.
    - lenv_tac.
    - unfold lres, numa_cap; rewrite (proj2 (Z.eqb_neq (p_h v) 0)) by lia; fold mch;
      repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
      cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *;
      repeat lazymatch goal with |- _ /\ _ => split end; [lia | lia | lia | exact LVP]. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [lvsub]| solve [frames_sub_tac]| lia] | exact I]).
  unfold numa_cap in *. rewrite (proj2 (Z.eqb_neq (p_h v) 0)) in * by lia.
  lazymatch goal with H : rt_live RT ?S = numa_live ?p _ ?q _ |- _ => rename H into LVN; rename S into Σn; set (na := p) in *; set (arr := q) in * end.
  lazymatch goal with H : numa_obj _ _ na _ arr [] |- _ => rename H into NOBJ end.
  lazymatch goal with A : ART RT Σn _ |- _ => rename A into ARTN end. pose proof ARTN as ARTN'.
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (_ & NCAP & NA0 & NA16 & AR0 & AR16 & INNA & INAR & NANE).
  assert (FRSn : rt_frames RT Σn = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σn = _ |- _ => rewrite E end; exact FRS).
  assert (LVSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σn)) by (intros e He; rewrite LVN; unfold numa_live; right; right; repeat match goal with E : rt_live _ _ = _ |- _ => rewrite <- E end; first [exact He | repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He]).
  assert (LVSH : rt_live RT Σn = (arr, 4 * p_h v) :: (na, 32) :: rt_live RT Σ) by (rewrite LVN; unfold numa_live; repeat match goal with E : rt_live _ _ = rt_live RT Σ |- _ => rewrite E end; reflexivity).
  assert (LVBn : Z.of_nat (length (rt_live RT Σn)) + 0 <= LIVE_MAX) by (rewrite LVSH; cbn [length]; unfold LIVE_MAX in *; lia).
  assert (LVPn : forall p n, In (p, n) (rt_live RT Σn) -> 0 < n) by (intros p n Hp; rewrite LVSH in Hp; cbn [In] in Hp; destruct Hp as [Hp|[Hp|Hp]]; [injection Hp as <- <-; lia| injection Hp as <- <-; lia| exact (LVP p n Hp)]).
  assert (NCA : forall a, PF a -> a < na \/ na + 32 <= a).
  { intros a Ha. apply (live_chunk_apart RT AF Σn _ [(arr, 4 * p_h v)] na 32 (rt_live RT Σ) (rt_live RT Σ) (rt_frames RT Σn) usp a ARTN);
      [rewrite LVSH; reflexivity| intros e He; apply in_or_app; right; exact He| reflexivity| repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia|].
    apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRSn; solve [frames_sub_tac]| lia]. }
  assert (NCB : forall a, PF a -> a < arr \/ arr + 4 * p_h v <= a).
  { intros a Ha. apply (live_chunk_apart RT AF Σn _ [] arr (4 * p_h v) ((na, 32) :: rt_live RT Σ) (rt_live RT Σ) (rt_frames RT Σn) usp a ARTN);
      [rewrite LVSH; reflexivity| intros e He; right; exact He| reflexivity| repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia|].
    apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRSn; solve [frames_sub_tac]| lia]. }
  chunk_facts RT AF GP na 32. chunk_facts RT AF GP arr (4 * p_h v).
  fframe_chunk RT AF fr 1%nat 128 na 32. fframe_chunk RT AF fr 1%nat 128 arr (4 * p_h v).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  pwalk_to AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixGetLastOffPixelInRun; e_numaCreate].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with MUx : munch _ _ _ |- _ => kl_of_munch KL (rt_live RT Σn) MUx fr ARTN' FRSn LOW LOR; apply (numa_obj_keep _ _ _ na (p_h v) arr [] KL) in NOBJ; clear KL end.
  split_off FR 48 FRL.
  lazymatch type of FRL with rw_cells _ _ _ (CB ?n ?jj :: ?rest) =>     (* [comment removed for export] *)
      let r := eval vm_compute in (n - 8)%nat in
      lazymatch r with
      | O => apply (rw_cells_split_CB asegs _ _ [] n jj rest [4; 4]%nat) in FRL
      | _ => apply (rw_cells_split_CB asegs _ _ [] n jj rest [4; 4; r]%nat) in FRL
      end; [| reflexivity]; cbn [mk_CB_cells app] in FRL end.
  split_at FRL 1%nat FRL2. split_at FRL2 1%nat FRR.
  destruct (cb4_c4 _ _ _ FRL2) as (lold & LOCC). clear FRL2.
  eapply cps_seq.
  { eapply SCANOFF with (lo := lo) (pix := pix) (ploc := usp + -108) (x := p_w v - 1) (y := 0) (v := v) (cv := cv) (old := lold).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - split; [lia| reflexivity].
  - split; [lia| reflexivity].
  - reflexivity.
  - reflexivity.
  - lazymatch goal with |- pix_obj _ ?mc _ _ _ =>
          assert (KL0 : keeps_live (rt_live RT Σ) m mc) by (intros b kk Hb a Ha; apply AGF; exact (PML b kk _ Hb Ha));
          unfold hid in POBJ; exact (pix_obj_mono _ _ mc pix v cv LVSUB (pix_obj_keep _ m mc pix v cv KL0 POBJ)) end.
  - exact D1.
  - exact VDATA.
  - lia.
  - lia.
  - replace (usp + -108) with ((usp + -160) + 52) by lia; apply (optrS_frame (usp + -160) 52); [change (2^64) with 18446744073709551616; lia| lia| unfold USTACK_TOP; lia| clear - AL SPA; Z.div_mod_to_equations; lia| reflexivity].
  - exact LOCC.
  - lenv_tac.
  - unfold lres, SCANOFF_COST; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
        lazymatch goal with |- context [rt_live RT ?S] => replace (rt_live RT S) with (rt_live RT Σn) by (symmetry; eqv) | _ => idtac end;
        cbn [length]; unfold FRAMES_MAX in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; repeat split; [lia| exact LVBn | subst mch hw2; lia| exact LVPn].
  }
  after_call RT AF.
  lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      kl_of_ag KL (rt_live RT Σn) AGx fr ARTN' FRSn LOW LOR; apply (numa_obj_keep _ _ _ na (p_h v) arr [] KL) in NOBJ; clear KL end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [lvsub]| solve [frames_sub_tac]| lia] | cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]]).
  lazymatch goal with H1 : 0 <= ?r, H2 : ?r <= p_w v - 1 + 1 |- _ => rename r into rr; rename H1 into RR0; rename H2 into RR1 end.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  pwalk_to AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_numaAddNumber; e_pixGetLastOffPixelInRun].
  (* [comment removed for export] *)
  rewrite ?(sx32_s32 rr) by lia.
  lazymatch goal with
    | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
        eapply (evt_cut segs (fun ms' => exists q : Z, 1 <= q <= p_w v /\
                   ms' = MS (@bvmap_set 5 word (Z_to_bv 5 11) (Z_to_bv 64 q) R) F (Z_to_bv 64 0x12cc7c) fc rv mm ro));
        [ | let q := fresh "q" in let Hq := fresh "Hq" in let E := fresh "E" in
            let ms := fresh "ms" in intros ms (q & Hq & E); subst ms; norm_regset ]
    end.
  { destruct (Z.eq_dec rr 0) as [RZ|RZ].
  - rewrite RZ in *.
  brF.
  pwalk [0x12cc7c].
  sx32_fix.
  apply evt_done; exists (p_w v); split; [lia| norm_regset; reflexivity].
  - brT.
  apply evt_done; exists rr; split; [lia| norm_regset; reflexivity].
  }
  pwalk [e_numaAddNumber; e_pixGetLastOffPixelInRun].
  (* [comment removed for export] *)
  assert (LOC0a : 0 <= q + -1) by lia. assert (LOC0b : q + -1 <= p_w v - 1) by lia.
  set (loc0 := q + -1) in *. clearbody loc0.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with MUx : munch _ _ _ |- _ => kl_of_munch KL (rt_live RT Σn) MUx fr ARTN' FRSn LOW LOR; apply (numa_obj_keep _ _ _ na (p_h v) arr [] KL) in NOBJ; clear KL end.
  eapply cps_seq.
  { eapply NADDF with (lo := lo) (na := na) (cap := p_h v) (arr := arr) (vals := []) (v := ival_w loc0).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - unfold freg_is, ival_w, fa0; apply freg_get_same; reflexivity.
  - lazymatch goal with |- numa_obj (rt_live RT ?S) ?mc _ _ _ _ => replace (rt_live RT S) with (rt_live RT Σn) by (symmetry; eqv) end; exact NOBJ.
  - cbn [length Z.of_nat]; lia.
  - lenv_tac.
  - unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
        lazymatch goal with |- context [rt_live RT ?S] => replace (rt_live RT S) with (rt_live RT Σn) by (symmetry; eqv) end;
        cbn [length]; unfold FRAMES_MAX, SCANOFF_COST in *; repeat split; [lia| exact LVBn | lia| exact LVPn].
  }
  clear NOBJ.
  after_call RT AF.
  lazymatch goal with H : numa_obj _ _ na _ arr (_ ++ _) |- _ => rename H into NOBJ end.
  lazymatch type of NOBJ with numa_obj (rt_live RT ?S) _ _ _ _ _ => replace (rt_live RT S) with (rt_live RT Σn) in NOBJ by (symmetry; eqv) | _ => idtac end.
  cbn [app] in NOBJ. change [ival_w loc0] with (map ival_w [loc0]) in NOBJ.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [lvsub]| solve [frames_sub_tac]| lia] | cbn [outside]; pose proof (NCA _ Hx); pose proof (NCB _ Hx); repeat split; try exact I; lia]).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  pwalk_to AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x12cfbc; 0x12cca0].
  (* [comment removed for export] *)
  sx32_fix. rewrite ?(sx32_small (p_h v)) by lia.
  destruct (Z_lt_ge_dec (p_h v) 2) as [HONE|HTWO].
  - brT.
  assert (KS1 : Z.of_nat (length [loc0]) = p_h v) by (cbn; lia).
  assert (KSF1 : Forall (fun q => loc_ok q /\ q <= p_w v - 1) [loc0]) by (constructor; [unfold loc_ok, LOC_LO, LOC_HI; lia| constructor]).
  revert KS1 KSF1 NOBJ. generalize [loc0] as ks. intros ks KS1 KSF1 NOBJ.
  lazymatch goal with |- evt _ (fun ms' => cps _ (ASTA RT ?S _ _) _) _ =>
        assert (CRX : rt_credit RT Σ - (hw2 + mch + 2) <= rt_credit RT S) by (repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; unfold GETPIXEL_COST, SCANOFF_COST in *; lia) end.
  pwalk [0x12cbc0].
    lazymatch goal with MUx : munch _ _ _ |- _ => kl_of_munch KL (rt_live RT Σn) MUx fr ARTN' FRSn LOW LOR; apply (numa_obj_keep _ _ _ na (p_h v) arr _ KL) in NOBJ; clear KL end.
    frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x12cbc8
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    lazymatch goal with K : forall b kk, In (b, kk) (rt_live RT ?S) -> forall a : word, _ -> ?m2 a = ?m1 a |- _ =>
          let KL := fresh "KL" in
          assert (KL : keeps_live (rt_live RT Σn) m1 m2)
            by (let b := fresh "b" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
                intros b kk Hb a Ha; apply (K b kk); [ in_live_eq Hb | exact Ha ]);
          apply (numa_obj_keep _ _ _ na (p_h v) arr _ KL) in NOBJ; clear KL K end.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    lazymatch goal with H : rw_cells asegs _ (usp + -108) _ |- _ => rename H into LOCX end.
    join_cells FR FRL. join_cells FR LOCX. join_cells FR FRR.
    walk_to AF MST [(usp - 224, usp)] (@nil Z).
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, na, arr, ks end.
    split.
    2: {
    split; [exact KS1|]. split; [exact KSF1|]. split; [first [eqv | unfold numa_live in *; eqv]|]. split; [eqv|]. split; [eqv|].
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia.
    }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto 20 using wmono_trans.
    }
    split; [intros a Ha _; exact (AGF a Ha)|].
    lazymatch goal with |- numa_obj (rt_live RT ?S) _ _ _ _ _ => replace (rt_live RT S) with (rt_live RT Σn) by (symmetry; eqv) end. exact NOBJ.
  - brF.
  pwalk [0x12ccdc; 0x12cfbc].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                           repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  lazymatch goal with MUx : munch _ _ _ |- _ => kl_of_munch KL (rt_live RT Σn) MUx fr ARTN' FRSn LOW LOR; apply (numa_obj_keep _ _ _ na (p_h v) arr _ KL) in NOBJ; clear KL end.
  rewrite ?(sx32_small (p_w v)) in FRM by lia. rewrite ?(sx32_small (p_h v)) in FRM by lia.
  split_off FRM 32 FW. split_at FW 1%nat FG1. split_at FG1 1%nat FH. split_at FH 1%nat FG2.
  lazymatch type of FG2 with rw_cells _ _ _ (CB 68 ?jj :: ?rest) =>
        apply (rw_cells_split_CB asegs _ _ [] 68 jj rest [28; 4; 36]%nat) in FG2; [| reflexivity]; cbn [mk_CB_cells app] in FG2 end.
  split_at FG2 1%nat FVP. split_at FVP 1%nat FG3. destruct (cb4_c4 _ _ _ FVP) as (vp & VALP). clear FVP.
  split_at FSH 10%nat SH10. split_at SH10 1%nat SHhi.
  lazymatch goal with H : rw_cells asegs _ (usp + -108) _ |- _ => rename H into LOCX end.
    eapply cps_seq.
    { eapply (row_loop RT AF GP GETPIX SCANOFF SCANON NADDF (Z.to_nat (p_h v - 1)) 1 loc0) with (lo := lo) (v := v) (cv := cv) (live := rt_live RT Σn) (live0 := rt_live RT Σ) (frames := rt_frames RT Σ) (ks := [loc0])
            (na := na) (arr := arr) (fr := fr) (spa := usp + -160) (vp := vp).
    - lia.
    - lia.
    - lia.
    - exact FDO.
    - exact MST.
    - eqv.
    - eqv.
    - exact LVSH.
    - lazymatch goal with |- pix_obj _ ?mc _ _ _ =>
              assert (KL0 : keeps_live (rt_live RT Σ) m mc) by (intros b kk Hb a Ha; apply AGF; exact (PML b kk _ Hb Ha));
              unfold hid in POBJ; exact (pix_obj_keep _ m mc pix v cv KL0 POBJ) end.
    - exact D1.
    - exact VDATA.
    - exact NOBJ.
    - cbn; lia.
    - constructor; [unfold loc_ok, LOC_LO, LOC_HI; lia| constructor].
    - replace (usp + -160 + 52) with (usp + -108) by lia; exact LOCX.
    - exact FW.
    - exact FH.
    - exact VALP.
    - exact SH10.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia.
    - unfold LSTK, RT_STACK; lia.
    - unfold USTACK_TOP; lia.
    - clear - AL SPA; Z.div_mod_to_equations; lia.
    - repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
    - lia.
    - exact FR64.
    - repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia.
    - unfold SEGTOP_A; lia.
    - clear - FRSH; unfold parked in *; lia.
    - lia.
    - exact LVBn.
    - repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; unfold GETPIXEL_COST, SCANOFF_COST in *; subst mch hw2; lia.
    - exact LVPn.
    }
    clear NOBJ.
    after_call RT AF.
    lazymatch goal with H : numa_obj _ _ na _ arr (map ival_w ?ks') |- _ => rename H into NOBJ; rename ks' into ks end.
    lazymatch type of NOBJ with numa_obj (rt_live RT ?S) _ _ _ _ _ => replace (rt_live RT S) with (rt_live RT Σn) in NOBJ by (symmetry; eqv) | _ => idtac end.
    lazymatch goal with H1 : Z.of_nat (length ks) = p_h v, H2 : Forall _ ks |- _ => rename H1 into KS1; rename H2 into KSF1 end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [lvsub]| solve [frames_sub_tac]| lia] | cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); pose proof (NCB _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]]).
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ =>
          assert (CRX : rt_credit RT Σ - (hw2 + mch + 2) <= rt_credit RT S) by (repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; unfold GETPIXEL_COST, SCANOFF_COST in *; subst hw2 mch; lia) end.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    pwalk_to AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x12cbc0].
    lazymatch goal with MUx : munch _ _ _ |- _ => kl_of_munch KL (rt_live RT Σn) MUx fr ARTN' FRSn LOW LOR; apply (numa_obj_keep _ _ _ na (p_h v) arr _ KL) in NOBJ; clear KL end.
    frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x12cbc8
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
          ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    lazymatch goal with K : forall b kk, In (b, kk) (rt_live RT ?S) -> forall a : word, _ -> ?m2 a = ?m1 a |- _ =>
          let KL := fresh "KL" in
          assert (KL : keeps_live (rt_live RT Σn) m1 m2)
            by (let b := fresh "b" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
                intros b kk Hb a Ha; apply (K b kk); [ in_live_eq Hb | exact Ha ]);
          apply (numa_obj_keep _ _ _ na (p_h v) arr _ KL) in NOBJ; clear KL K end.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    lazymatch goal with H : rw_cells asegs _ (usp + -160 + 52) _ |- _ => replace (usp + -160 + 52) with (usp + -108) in H by lia; rename H into LOCY end.
    join_cells FR FRL. join_cells FR LOCY. join_cells FR FRR.
    walk_to AF MST [(usp - 224, usp)] (@nil Z).
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, na, arr, ks end.
    split.
    2: {
    split; [exact KS1|]. split; [exact KSF1|]. split; [first [eqv | unfold numa_live in *; eqv]|]. split; [eqv|]. split; [eqv|].
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia.
    }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto 20 using wmono_trans.
    }
    split; [intros a Ha _; exact (AGF a Ha)|].
    lazymatch goal with |- numa_obj (rt_live RT ?S) _ _ _ _ _ => replace (rt_live RT S) with (rt_live RT Σn) by (symmetry; eqv) end. exact NOBJ.
Qed.
End PROFC.
