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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs D_libiface
  Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_chain Lept_leaf LeptC_leaf Lept_objkit Lept_fuzzkit Lept_gmax_defs LeptM_destroy_defs Ed_iface Ed_fpkit Ed_statics Ed_fuzz_defs Ed_meas_defs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Ed_fp Numa_kit Ed_numa_leaf Ed_numa_ival.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_trans Ed_meas_loop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Ltac rt_transport_extra m m' AG ::= meas_rt_transport_extra m m' AG.



(* [comment removed for export] *)
Ltac subfp_tac ::= clear; let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz; cbn [outside] in Hz |- *; unfold MLW; cbn [outside]; lia.
(* [comment removed for export] *)
Ltac at_cut RT AF ivt pft :=
  cps_stop; art_now RT AF ivt;
  lazymatch goal with
  | AGF : agree_on ?PF _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PF; agf_munch AGF MUx pft
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac obj_fwd NOBJ MU apart :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
  lazymatch type of NOBJ with numa_obj ?lv ma ?na ?c ?ar ?vs =>
    apply (numa_obj_keep lv ma mb na c ar vs) in NOBJ;
    [| let b := fresh "b" in let k := fresh "k" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
       intros b k Hin a Ha; apply MU; apart b k a Hin Ha ]
  end end.
Ltac obj_fwd_ag NOBJ AG inP :=
  lazymatch type of AG with agree_on ?P ?ma ?mb =>
  lazymatch type of NOBJ with numa_obj ?lv ma ?na ?c ?ar ?vs =>
    apply (numa_obj_keep lv ma mb na c ar vs) in NOBJ;
    [| let b := fresh "b" in let k := fresh "k" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
       intros b k Hin a Ha; apply AG; inP b k a Hin Ha ]
  end end.
(* [comment removed for export] *)
Ltac live_out RT AF S usp slo b k a Hin Ha :=
  lazymatch goal with A : ART RT S ?mm, FRSx : rt_frames RT S = (?fr, 1%nat) :: _ |- _ =>
    let O := fresh "O" in
    pose proof (live_outside_frame1 RT AF S mm fr usp slo b k (bv_unsigned a) A ltac:(rewrite FRSx; left; reflexivity)
                  ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia) Hin Ha) as O;
    cbn [outside] in O |- *; clear - O; repeat split; try exact I; lia end.
(* [comment removed for export] *)
Ltac art_here RT AF S lo ivt :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      lazymatch goal with
      | _ : ART RT S mf |- _ => idtac
      | A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
          let N := fresh "ARTh" in
          assert (N : ART RT S mf)
            by (apply (art_client_writes RT AF S mm mf lo W A MUx WMx);
                [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | ivt ])
      end
  end.
(* [comment removed for export] *)
Ltac acl_dispatch A ::=
  lazymatch A with
  | context [(_ / 8)%Z] => fframe_tac
  | _ =>
    let b := head_var A in
    lazymatch b with
    | Zpos _ =>
        let inb := eval vm_compute in (existsb (fun r => (fst r <=? b) && (b <? fst r + snd r))%Z LEPT_GLOBALS) in
        lazymatch inb with true => static_tac end
    | _ =>
      first [ lazymatch goal with _ : rt_frames _ _ = (b, _) :: _ |- _ => fframe_tac end
            | lazymatch goal with _ : In (b, _) _ |- _ =>
                match goal with
                | H : In (b, ?k) _ |- aclient _ _ _ ?x => right; right; left; exists b, k; split; [ solve [in_live_tac] | ul ]
                end end
            | lazymatch goal with _ : accok _ _ _ b _ |- _ =>
                match goal with
                | H : accok ?lv ?frs ?m b ?n |- aclient ?lv' ?frs' ?sp' ?x =>
                    apply (aclient_mono lv frs sp' lv' frs' sp' x);
                    [ exact (accok_aclient lv frs m sp' b n x H ltac:(ul)) | first [solve [live_sub_tac] | solve [live_add_tac]] | frames_sub_tac | lia ]
                end end
            | left; ul ]
    end
  end.
(* [comment removed for export] *)
Ltac acc_fwd ACC MU side :=
  lazymatch type of ACC with acc asegs ?m ?a ?n =>
    lazymatch type of MU with munch ?W m ?m' =>
      apply (fun h => acc_transport W m m' a n h MU ltac:(lia) ltac:(unfold shad, SHB; cbn [disjoint_from]; side)) in ACC
    end end.

Section MEAS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis REI : returnError_cps RT e_returnErrorInt.
Hypothesis PROFILE : pixGetEdgeProfile_cps RT.
Hypothesis EXTREMA : numaFindExtrema_cps RT.
Hypothesis NDESTROY : numaDestroy_cps RT.
  (* [comment removed for export] *)
Lemma meas_c0 : meas_case RT 0.
Proof using AF RC GP REI PROFILE EXTREMA NDESTROY.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pix p1 p2 p3 v cv o1 o2 o3 ras FDO MST -> -> -> -> -> -> -> -> -> POBJ VDATA OP1 OP2 OP3 CP1 CP2 CP3 P12 P23 UCX RA0 -> ENV RES AL.
  unfold lpost, lpost_f, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW0 & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). unfold uctx in UCX.
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & HDROK & PDAT & PCM).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0. change (2 ^ Z.of_N 64) with (2^64) in RS0.
  unfold entry_st, e_pixMeasureEdgeSmoothness, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, MEASURE_COST in *.
  assert (PC0 : 0 <= PROFILE_COST (p_w v) (p_h v)).
  { clear - HDROK. destruct HDROK as (_ & HW & HH & _). unfold PROFILE_COST, mcost. destruct (4 * p_h v <=? 64512); nia. }
  assert (EC0 : 0 <= EXTREMA_COST) by (unfold EXTREMA_COST, EXTREMA_GROWTH_COST, mcost; cbn; lia).
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(p1, p1 + 4); (p2, p2 + 4); (p3, p3 + 4)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  set (PF0 := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  assert (PFS0 : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pix 64.
  destruct HDROK as (HDd & HW & HH & HWPL & HRS).
  assert (DBND : 1 <= p_d v <= 32) by (clear - HDd; cbn [In] in HDd; lia).
  pose proof (measure_cost_bound (p_w v) (p_h v) HW HH) as MCB. unfold MEASURE_COST in MCB.
  destruct OP1 as (OWN1 & P1a & P1b & P1c & P1d). destruct OP2 as (OWN2 & P2a & P2b & P2c & P2d). destruct OP3 as (OWN3 & P3a & P3b & P3c & P3d).
  assert (AK1 : accok (rt_live RT Σ) (rt_frames RT Σ) m p1 4) by (right; exact OWN1).
  assert (AK2 : accok (rt_live RT Σ) (rt_frames RT Σ) m p2 4) by (right; exact OWN2).
  assert (AK3 : accok (rt_live RT Σ) (rt_frames RT Σ) m p3 4) by (right; exact OWN3).
  pose proof AK1 as AKc1. hide AKc1. pose proof AK2 as AKc2. hide AKc2. pose proof AK3 as AKc3. hide AKc3.
  assert (P1S : p1 + 12 <= rt_sp0 RT Σ - 8388608 /\ forall p n, In (p, n) (rt_live RT Σ) -> p1 + 4 <= p \/ p + n <= p1).
  { destruct OWN1 as (f & k & FIN & Fa & Fb & _). pose proof (af_frames_range RT AF Σ m f k ART0 FIN) as (_ & R2 & _ & R4).
    unfold STACK_WIN in R2. split; [lia|]. intros p n Hp. destruct (R4 p n Hp); lia. }
  assert (P2S : p2 + 12 <= rt_sp0 RT Σ - 8388608 /\ forall p n, In (p, n) (rt_live RT Σ) -> p2 + 4 <= p \/ p + n <= p2).
  { destruct OWN2 as (f & k & FIN & Fa & Fb & _). pose proof (af_frames_range RT AF Σ m f k ART0 FIN) as (_ & R2 & _ & R4).
    unfold STACK_WIN in R2. split; [lia|]. intros p n Hp. destruct (R4 p n Hp); lia. }
  assert (P3S : p3 + 12 <= rt_sp0 RT Σ - 8388608 /\ forall p n, In (p, n) (rt_live RT Σ) -> p3 + 4 <= p \/ p + n <= p3).
  { destruct OWN3 as (f & k & FIN & Fa & Fb & _). pose proof (af_frames_range RT AF Σ m f k ART0 FIN) as (_ & R2 & _ & R4).
    unfold STACK_WIN in R2. split; [lia|]. intros p n Hp. destruct (R4 p n Hp); lia. }
  destruct P1S as [P1S P1L]. destruct P2S as [P2S P2L]. destruct P3S as [P3S P3L].
  pose proof (P1L pix 64 PIN) as P1X. pose proof (P2L pix 64 PIN) as P2X. pose proof (P3L pix 64 PIN) as P3X.
  hide OWN1. hide OWN2. hide OWN3. unfold pix_cells in PXC.
  hide POBJ. hide PCM. hide UCX.
  park_disj. carve_frame 192%nat ST.
  clear_acc.
  walk_to AF MST [(usp - 192, usp)] [e_stack_malloc 1%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S0 end.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
  fframe_chunk RT AF fr 1%nat 128 pix 64.
  lazymatch goal with A : ART RT S0 ?mm |- _ =>
    assert (NFA0 : forall a, PF0 a -> (a < fr \/ fr + 128 <= a) /\ (a < shad fr \/ shad (fr + 128) <= a))
      by (intros a Ha; apply (new_frame_apart RT AF S0 mm fr 1%nat (rt_frames RT Σ) (rt_live RT Σ) usp a A FRS);
          [ intros e He; repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; lia
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
          | exact Ha ]) end.
  assert (P1F : (p1 + 4 <= fr \/ fr + 128 <= p1) /\ (p1 + 4 <= fr / 8 + 2147450880 \/ fr / 8 + 2147450880 + 16 <= p1)).
  { pose proof (NFA0 p1 (accok_aclient _ _ _ usp p1 4 p1 AK1 ltac:(lia))) as [A1 B1].
    pose proof (NFA0 (p1 + 3) (accok_aclient _ _ _ usp p1 4 (p1 + 3) AK1 ltac:(lia))) as [A2 B2].
    unfold shad, SHB in A1, B1, A2, B2. clear - A1 B1 A2 B2 FR64. split; Z.div_mod_to_equations; lia. }
  assert (P2F : (p2 + 4 <= fr \/ fr + 128 <= p2) /\ (p2 + 4 <= fr / 8 + 2147450880 \/ fr / 8 + 2147450880 + 16 <= p2)).
  { pose proof (NFA0 p2 (accok_aclient _ _ _ usp p2 4 p2 AK2 ltac:(lia))) as [A1 B1].
    pose proof (NFA0 (p2 + 3) (accok_aclient _ _ _ usp p2 4 (p2 + 3) AK2 ltac:(lia))) as [A2 B2].
    unfold shad, SHB in A1, B1, A2, B2. clear - A1 B1 A2 B2 FR64. split; Z.div_mod_to_equations; lia. }
  assert (P3F : (p3 + 4 <= fr \/ fr + 128 <= p3) /\ (p3 + 4 <= fr / 8 + 2147450880 \/ fr / 8 + 2147450880 + 16 <= p3)).
  { pose proof (NFA0 p3 (accok_aclient _ _ _ usp p3 4 p3 AK3 ltac:(lia))) as [A1 B1].
    pose proof (NFA0 (p3 + 3) (accok_aclient _ _ _ usp p3 4 (p3 + 3) AK3 ltac:(lia))) as [A2 B2].
    unfold shad, SHB in A1, B1, A2, B2. clear - A1 B1 A2 B2 FR64. split; Z.div_mod_to_equations; lia. }
  destruct P1F as [P1F P1FS]. destruct P2F as [P2F P2FS]. destruct P3F as [P3F P3FS].
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  idtac "M0_DONE".
  (* [comment removed for export] *)
  park AK1. park AK2. park AK3. park CP1. park CP2. park CP3.
  walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x120e98].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    unpark_accok_munch AK1 MUx (rt_live RT Σ) (rt_frames RT Σ) usp
        ltac:(fun Hx => cbn [outside]; pose proof (PFS0 _ Hx); destruct (NFA0 _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    unpark_accok_munch AK2 MUx (rt_live RT Σ) (rt_frames RT Σ) usp
        ltac:(fun Hx => cbn [outside]; pose proof (PFS0 _ Hx); destruct (NFA0 _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    unpark_accok_munch AK3 MUx (rt_live RT Σ) (rt_frames RT Σ) usp
        ltac:(fun Hx => cbn [outside]; pose proof (PFS0 _ Hx); destruct (NFA0 _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    unpark_cells_munch CP1 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p1 4 _ AK1 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    unpark_cells_munch CP2 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p2 4 _ AK2 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    unpark_cells_munch CP3 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p3 4 _ AK3 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  assert (FRS0 : rt_frames RT S0 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (LV0 : rt_live RT S0 = rt_live RT Σ) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity).
  idtac "M1_DONE".
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (p1, p1 + 4); (p2, p2 + 4); (p3, p3 + 4)]
          [0x1210a4; 0x120efc].
  idtac "M2_WALKED".
  (* [comment removed for export] *)
  rewrite (sx32_small (p_d v)) by lia.
  destruct (Z.eq_dec (p_d v) 1) as [D1|DN1].
  all: cycle 1.
  (* [comment removed for export] *)
  brT.
  awalk [e_returnErrorInt].
  idtac "AT_REI".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                            split; [intros zz Hzz; acl_ak AKc1 | split; [intros zz Hzz; acl_ak AKc2 | split; [intros zz Hzz; acl_ak AKc3 | exact I]]]]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
  idtac "AT_CALL_OK".
  pose proof REI as RE. unfold returnError_cps in RE.
  eapply cps_seq.
  { eapply RE with (lo := lo); rt_side idtac; [lit_in_fast | lit_in_fast | lenv_tac | lres_tac..]. }
  idtac "REI_APPLIED".
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  idtac "M3_DONE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  park CP1. park CP2. park CP3.
  walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x12127c].
  idtac "M4_AT_FLAG".
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    unpark_cells_munch CP1 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p1 4 _ AKc1 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    unpark_cells_munch CP2 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p2 4 _ AKc2 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    unpark_cells_munch CP3 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p3 4 _ AKc3 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  frame_release_w RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x121284
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact (proj1 Hx))
      ltac:(fun fl FLN =>
              assert (FLP1 : fl < p1 \/ p1 + 4 <= fl)
                by (destruct (Z_lt_ge_dec fl p1) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (p1 + 4)) as [FG2|]; [| right; lia]; exfalso; apply FLN;
                    apply (aclient_mono _ _ 140737488355328 _ _ _ _ (accok_aclient _ _ _ 140737488355328 p1 4 fl AKc1 ltac:(lia)));
                    [solve [live_sub_tac] | solve [frames_sub_tac] | ul]);
              assert (FLP2 : fl < p2 \/ p2 + 4 <= fl)
                by (destruct (Z_lt_ge_dec fl p2) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (p2 + 4)) as [FG2|]; [| right; lia]; exfalso; apply FLN;
                    apply (aclient_mono _ _ 140737488355328 _ _ _ _ (accok_aclient _ _ _ 140737488355328 p2 4 fl AKc2 ltac:(lia)));
                    [solve [live_sub_tac] | solve [frames_sub_tac] | ul]);
              assert (FLP3 : fl < p3 \/ p3 + 4 <= fl)
                by (destruct (Z_lt_ge_dec fl p3) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (p3 + 4)) as [FG2|]; [| right; lia]; exfalso; apply FLN;
                    apply (aclient_mono _ _ 140737488355328 _ _ _ _ (accok_aclient _ _ _ 140737488355328 p3 4 fl AKc3 ltac:(lia)));
                    [solve [live_sub_tac] | solve [frames_sub_tac] | ul])).
  idtac "M4_RELEASED".
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 208, usp)] (@nil Z).
  (* [comment removed for export] *)
  idtac "M4_AT_RET".
  cps_stop.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  lazymatch type of CP1 with rw_cells _ _ _ [C4 ?y] => eexists; exists y end.
  lazymatch type of CP2 with rw_cells _ _ _ [C4 ?y] => exists y end.
  lazymatch type of CP3 with rw_cells _ _ _ [C4 ?y] => exists y end.
  split; [| alg_tac].
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; assumption] | split; assumption]|].
  split.
  { intros a Ha Ho. apply AGF. split; [| exact Ho].
    revert Ha. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. intros Ha. exact Ha. }
  split; [exact CP1 | split; [exact CP2 | exact CP3]].
  idtac "M4_ARM_DONE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  brF.
  awalk [e_pixGetEdgeProfile].
  idtac "M5_AT_PROFILE".
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                            split; [intros zz Hzz; acl_ak AKc1 | split; [intros zz Hzz; acl_ak AKc2 | split; [intros zz Hzz; acl_ak AKc3 | exact I]]]]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
  idtac "M5_ATCALL".
  (* [comment removed for export] *)
  lazymatch type of AGF with agree_on _ _ ?mc =>
    assert (KL : keeps_live (rt_live RT Σ) m mc)
      by (intros bb kk Hin aa Ha; apply AGF; split;
          [ right; right; left; exists bb, kk; split; [exact Hin | exact Ha]
          | cbn [outside]; pose proof (P1L bb kk Hin); pose proof (P2L bb kk Hin); pose proof (P3L bb kk Hin); repeat split; try exact I; lia ]);
    unfold hid in POBJ; pose proof (pix_obj_keep _ m mc pix v cv KL POBJ) as POBJc; hide POBJ;
    unfold hid in UCX;
    assert (UCXc : chain_ok mc usp (bv_unsigned s0) [RA_TOP])
      by (apply (chain_ok_keep [RA_TOP] m mc usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; split;
          [ left; exact Hzx | cbn [outside]; repeat split; try exact I; lia ]);
    hide UCX end.
  idtac "M5_FACTS".
  pose proof PROFILE as PRF. unfold pixGetEdgeProfile_cps in PRF.
  eapply cps_seq.
  { eapply PRF with (lo := lo) (pix := pix) (v := v) (cv := cv) (ras := MEAS_RAS); rt_side idtac.
    all: lazymatch goal with
         | |- pix_obj _ _ _ _ _ => rewrite LV0; exact POBJc
         | |- p_d _ = 1 => exact D1
         | |- p_data _ <> 0 => exact VDATA
         | |- uctx _ _ _ _ =>
             unfold uctx, MEAS_RAS; rewrite ?unsigned_lit by ul; rewrite <- RA0;
             apply (chain_ok_push _ (usp + -192) usp (bv_unsigned ra) (bv_unsigned s0) [RA_TOP]);
               [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | rewrite RA0; unfold RA_FUZZ_MEASURE; lia | apply bv_unsigned_in_range
               | rewrite !Z_to_bv_bv_unsigned; exact FRrec2
               | exact UCXc ]
         | |- numaCreate_trace_ok _ => rewrite ?unsigned_lit by ul; exact tr_meas_profile
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "LEFT:" g
         end. }
  idtac "M5_PROFILE_APPLIED".
  idtac "M5_PROFILE_APPLIED".
  after_call RT AF.
  idtac "M5_AFTERCALL".
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia] | exact I]).
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S1 end.
  unfold numa_live in *.
  lazymatch goal with H : numa_obj _ _ ?nav (p_h v) ?arrv (map ival_w ?ksv) |- _ => rename H into NOBJ; set (na := nav) in *; set (arr := arrv) in *; set (ks := ksv) in * end.
  idtac "M5_DONE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (NLEN & NCAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NNE).
  rewrite length_map in NLEN.
  destruct NOBJ as ((npad & NC) & (njunk & NA) & CHn & CHa & _).
  unfold numa_cells in NC. rewrite length_map in NC. park NA.
  assert (FRS1 : rt_frames RT S1 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  chunk_facts RT AF GP na 32. chunk_facts RT AF GP arr (4 * p_h v).
  fframe_chunk RT AF fr 1%nat 128 na 32. fframe_chunk RT AF fr 1%nat 128 arr (4 * p_h v).
  lazymatch goal with A : ART RT S1 ?mm |- _ =>
    unfold hid in OWN1, OWN2, OWN3;
    pose proof (own_frame_live_apart RT AF S1 mm m _ p1 4 na 32 A OWN1 ltac:(frames_sub_tac) INn) as P1N;
    pose proof (own_frame_live_apart RT AF S1 mm m _ p2 4 na 32 A OWN2 ltac:(frames_sub_tac) INn) as P2N;
    pose proof (own_frame_live_apart RT AF S1 mm m _ p3 4 na 32 A OWN3 ltac:(frames_sub_tac) INn) as P3N;
    pose proof (own_frame_live_apart RT AF S1 mm m _ p1 4 arr (4 * p_h v) A OWN1 ltac:(frames_sub_tac) INa) as P1A;
    pose proof (own_frame_live_apart RT AF S1 mm m _ p2 4 arr (4 * p_h v) A OWN2 ltac:(frames_sub_tac) INa) as P2A;
    pose proof (own_frame_live_apart RT AF S1 mm m _ p3 4 arr (4 * p_h v) A OWN3 ltac:(frames_sub_tac) INa) as P3A;
    hide OWN1; hide OWN2; hide OWN3 end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc.
  refresh RT AF. park_disj.
  idtac "M6_FACTS".
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (p1, p1 + 4); (p2, p2 + 4); (p3, p3 + 4)]
          [0x121094; 0x120f40].
  idtac "M6_WALKED".
  (* [comment removed for export] *)
  rewrite (sx32_small (Z.of_nat (length ks))) by lia.
  match goal with H : Z.of_nat (length ks) = p_h v |- _ => rename H into KLEN end.
  destruct (Z.eq_dec (p_h v) 1) as [HEQ1|HNE1].
  (* [comment removed for export] *)
  rewrite KLEN. rewrite HEQ1.
  awalk [e_numaDestroy].
  idtac "M7_AT_NDESTROY".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                            split; [intros zz Hzz; acl_ak AKc1 | split; [intros zz Hzz; acl_ak AKc2 | split; [intros zz Hzz; acl_ak AKc3 | exact I]]]]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
  idtac "M7_ATCALL".
  (* [comment removed for export] *)
  lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    unpark_na_munch NA MUx ltac:(fun Hx => unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  idtac "M7_NA".
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (NOBJc : numa_obj (rt_live RT S1) mc na (p_h v) arr (map ival_w ks))
      by (split; [exists npad; unfold numa_cells; rewrite length_map; exact NC
                | split; [exists njunk; exact NA | split; [exact CHn | split; [exact CHa | split; [exact NNE | rewrite length_map; split; [exact NCAP | exact NLEN]]]]]]) end.
  idtac "M7_NOBJ".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  split_at FRM 4%nat PNAc. split_at PNAc 1%nat FRM2.
  pose proof FSH as SHc. split_at SHc 8%nat SB8. split_at SB8 1%nat SB8r. clear SHc SB8r.
  idtac "M7_SLOT".
  pose proof NDESTROY as ND. unfold numaDestroy_cps in ND.
  eapply cps_seq;
    [ eapply ND with (lo := lo) (pna := fr + 64) (na := na) (cap := p_h v) (arr := arr) (vals := map ival_w ks); rt_side idtac;
      lazymatch goal with
         | |- optrF _ _ _ _ 8 =>
             unfold optrF, own_frame; split;
             [ exists fr, 1%nat; rewrite FRS1; change (fs_size 1) with 128;
               split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [lia|]; split; [pose proof (af_sp0_range RT AF Σ m ART0) as SPR; clear - FRHI SPR; unfold USTACK_TOP, STACK_WIN, SEGTOP_A in *; lia|]; change (ushadow 8) with [Z_to_bv 8 0];
               replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
               destruct SB8 as [[_ B] _]; exact B
             | unpark FRSH; unfold SEGTOP_A in *; clear - FR64 FR0 FRSH FRSEG; repeat split; first [lia | Z.div_mod_to_equations; lia] ]
         | |- rw_cells _ _ _ [C8 _] => exact PNAc
         | |- numa_obj _ _ _ _ _ _ => exact NOBJc
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         end
    | ].
  idtac "M7_ND_APPLIED".
  meas_after_call RT AF ltac:(idtac;
    lazymatch goal with H : rt_live RT ?S2 = numa_gone na arr (rt_live RT S1), A : ART RT S1 ?mm |- _ =>
      rewrite (numa_gone_live RT AF S1 mm na (p_h v) arr (rt_live RT Σ) A) in H;
      [ | repeat match goal with E : rt_live RT _ = _ |- _ => rewrite E end; reflexivity | lia
      | let pp := fresh "pp" in let nn := fresh "nn" in let Hpn := fresh "Hpn" in
        intros pp nn Hpn; apply (LVP pp nn); revert Hpn; repeat match goal with E : rt_live RT _ = _ |- _ => rewrite E end; intros Hpn; exact Hpn ] end).
  idtac "M7_AFTERCALL".
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S2 end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; repeat split; try exact I; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  idtac "M7E_DONE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  park CP1. park CP2. park CP3.
  walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x12127c].
  idtac "M8_AT_FLAG".
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    unpark_cells_munch CP1 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p1 4 _ AKc1 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    unpark_cells_munch CP2 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p2 4 _ AKc2 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    unpark_cells_munch CP3 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p3 4 _ AKc3 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  frame_release_w RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x121284
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact (proj1 Hx))
      ltac:(fun fl FLN =>
              assert (FLP1 : fl < p1 \/ p1 + 4 <= fl)
                by (destruct (Z_lt_ge_dec fl p1) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (p1 + 4)) as [FG2|]; [| right; lia]; exfalso; apply FLN;
                    apply (aclient_mono _ _ 140737488355328 _ _ _ _ (accok_aclient _ _ _ 140737488355328 p1 4 fl AKc1 ltac:(lia)));
                    [solve [live_sub_tac] | solve [frames_sub_tac] | ul]);
              assert (FLP2 : fl < p2 \/ p2 + 4 <= fl)
                by (destruct (Z_lt_ge_dec fl p2) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (p2 + 4)) as [FG2|]; [| right; lia]; exfalso; apply FLN;
                    apply (aclient_mono _ _ 140737488355328 _ _ _ _ (accok_aclient _ _ _ 140737488355328 p2 4 fl AKc2 ltac:(lia)));
                    [solve [live_sub_tac] | solve [frames_sub_tac] | ul]);
              assert (FLP3 : fl < p3 \/ p3 + 4 <= fl)
                by (destruct (Z_lt_ge_dec fl p3) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (p3 + 4)) as [FG2|]; [| right; lia]; exfalso; apply FLN;
                    apply (aclient_mono _ _ 140737488355328 _ _ _ _ (accok_aclient _ _ _ 140737488355328 p3 4 fl AKc3 ltac:(lia)));
                    [solve [live_sub_tac] | solve [frames_sub_tac] | ul])).
  idtac "M8_RELEASED".
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 208, usp)] (@nil Z).
  (* [comment removed for export] *)
  idtac "M8_AT_RET".
  cps_stop.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  lazymatch type of CP1 with rw_cells _ _ _ [C4 ?y] => eexists; exists y end.
  lazymatch type of CP2 with rw_cells _ _ _ [C4 ?y] => exists y end.
  lazymatch type of CP3 with rw_cells _ _ _ [C4 ?y] => exists y end.
  split; [| alg_tac].
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; assumption] | split; assumption]|].
  split.
  { intros a Ha Ho. apply AGF. split; [| exact Ho].
    revert Ha. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. intros Ha. exact Ha. }
  split; [exact CP1 | split; [exact CP2 | exact CP3]].
  idtac "M8_ARM_DONE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (LORP : 0 < Z.lor p1 p2).
  { pose proof (Z.lor_nonneg p1 p2) as L0. destruct (Z.eq_dec (Z.lor p1 p2) 0) as [E|NE]; [| lia].
    apply Z.lor_eq_0_iff in E. lia. }
  replace (0 <? Z.lor p1 p2) with true by (symmetry; apply Z.ltb_lt; exact LORP). change (Z.b2z true) with 1.
  rewrite KLEN. brF.
  idtac "M9_BR".
  (* [comment removed for export] *)
  at_cut RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                            split; [intros zz Hzz; acl_ak AKc1 | split; [intros zz Hzz; acl_ak AKc2 | split; [intros zz Hzz; acl_ak AKc3 | exact I]]]]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
  idtac "M9_CUT".
  (* [comment removed for export] *)
  lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    unpark_na_munch NA MUx ltac:(fun Hx => unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (NOBJ : numa_obj (rt_live RT S1) mc na (p_h v) arr (map ival_w ks))
      by (split; [exists npad; unfold numa_cells; rewrite length_map; exact NC
                | split; [exists njunk; exact NA | split; [exact CHn | split; [exact CHa | split; [exact NNE | rewrite length_map; split; [exact NCAP | exact NLEN]]]]]]) end.
  clear NC NA.
  assert (NINT : numa_ints (map ival_w ks) ks).
  { split; [reflexivity|]. match goal with H : Forall (fun k => loc_ok k /\ _) ks |- _ => clear - H; induction H as [|k0 l [A _] _ IH]; constructor; assumption end. }
  idtac "M9_NOBJ".
  (* [comment removed for export] *)
  split_at FRM 3%nat FRV. split_at FRV 1%nat PNAc. split_last_CB FRV [8; 4; 12; 4; 12]%nat.
  split_at FRV 1%nat CVAL. split_at CVAL 1%nat FRV2. split_at FRV2 1%nat CNVAL. split_at CNVAL 1%nat FRV3.
  destruct (cb4_c4 _ _ _ CVAL) as [ov CVALw]. destruct (cb4_c4 _ _ _ CNVAL) as [onv CNVALw]. clear CVAL CNVAL.
  split_at PNAc 1%nat FRV4.
  idtac "M9_CELLS".
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  local_acc FSH fr 4%nat 32 FR64 FR0 ACCV. local_acc FSH fr 6%nat 48 FR64 FR0 ACCNV.
  idtac "M9_ACC".
  walk_to AF MST [(usp - 208, usp); (fr + 32, fr + 36); (fr + 48, fr + 52)] [e_numaGetIValue].
  idtac "M9_AT_LEAF1".
  (* [comment removed for export] *)
  destruct (nth_error_ex' ks 0%nat ltac:(lia)) as [k0 Hk0].
  lazymatch goal with MI : mem_inv asegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (ed_ro_facts mc MI) as RO end.
  pose proof NOBJ as NOBJc.
  lazymatch goal with MUx : munch _ _ ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    obj_fwd NOBJc MUx ltac:(fun b k a Hin Ha => live_out RT AF S1 usp (usp - 208) b k a Hin Ha) end.
  idtac "M10_FACTS".
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ (frm_clear ?fc0) None ?mm _) =>
      eapply (numaGetIValue_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -192) lo (rt_live RT S1) na (p_h v) arr (map ival_w ks) ks 0 (fr + 32) k0 ov) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJc
         | |- numa_ints _ _ => exact NINT
         | |- nth_error _ _ = _ => exact Hk0
         | |- ED_RO _ => exact RO
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- rw_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | lazymatch goal with |- ?g => idtac "LEAF1 SIDE LEFT:" g end ]
         end. }
  idtac "M10_LEAF_APPLIED".
  (* [comment removed for export] *)
  intros ms' PO. unfold numaGetIValue_post in PO.
  destruct PO as (a1' & a2' & a3' & a4' & a5' & a6' & a7' & F1 & fc1 & mq1 & -> & MUl & WMl & MIl & STl & CVAL1).
  clear CVALw NOBJc RO.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    repeat match goal with H : stk asegs ma _ _ |- _ => clear H end;
    loop_art RT AF S1 mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; fframe_tac| exact I]]]);
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  clear MUl WMl.   (* [comment removed for export] *)
  fix_ret_pc.
  idtac "M11_LEAF1_DONE".
  (* [comment removed for export] *)
  awalk [0x120f80].
  idtac "M11_AT_LOOP".
  (* [comment removed for export] *)
  art_here RT AF S1 lo ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with A : ART RT S1 ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (acc_live RT AF S1 mc na 32 A INn) as ACCn; pose proof (acc_live RT AF S1 mc arr (4 * p_h v) A INa) as ACCa end.
  lazymatch goal with MI : mem_inv asegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (ed_ro_facts mc MI) as RO end.
  pose proof NOBJ as NOBJc.
  lazymatch goal with MUx : munch _ _ ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    obj_fwd NOBJc MUx ltac:(fun b k a Hin Ha => live_out RT AF S1 usp (usp - 208) b k a Hin Ha) end.
  (* [comment removed for export] *)
  pose proof FR as FRc. split_at FRc 2%nat SP16. split_at SP16 3%nat SP40. split_at SP40 1%nat SP48. split_at SP48 2%nat SP64. clear FRc SP40 SP64.
  pose proof FSH as SHc. split_at SHc 6%nat SB6. split_at SB6 1%nat SHc3. clear SHc SHc3.
  lazymatch type of SB6 with rw_cells _ ?mm _ _ =>
    assert (SHN : rw_cells asegs mm (fr / 8 + SHB + 6) [C1 (Z_to_bv 8 4)])
      by (unfold SHB; replace (fr / 8 + 2147450880 + 6) with (fr / 8 + 2147450886) by lia; exact SB6) end.
  clear SB6.
  assert (H2LE : 2 <= p_h v) by lia.
  idtac "M12_FACTS".
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ (frm_clear ?fc0) None ?mm _) =>
      eapply (meas_loop (Z.to_nat (p_h v - 1)) 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -192) fr lo (p_h v)
                (rt_live RT S1) na (p_h v) arr (map ival_w ks) ks (Z_to_bv 64 k0) onv) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJc
         | |- numa_ints _ _ => exact NINT
         | |- Z.of_nat (length _) = _ => exact KLEN
         | |- ED_RO _ => exact RO
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- rw_cells _ _ _ [C1 _] => exact SHN          (* [comment removed for export] *)
         | |- rw_cells _ _ ?A [C8 _; C8 _; C8 _] => lazymatch type of SP16 with rw_cells _ _ ?B _ => replace A with B by lia; exact SP16 end
         | |- rw_cells _ _ ?A [C8 _; C8 _] => lazymatch type of SP48 with rw_cells _ _ ?B _ => replace A with B by lia; exact SP48 end
         | |- rw_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- forall b kk x, In _ _ -> _ -> outside _ _ =>
             let b := fresh "b" in let kk := fresh "kk" in let x := fresh "x" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
             intros b kk x Hin Hx;
             lazymatch type of Hin with In _ (rt_live _ ?Sx) => lazymatch goal with A : ART _ Sx ?ma |- _ =>
               pose proof (live_outside_frame1 RT AF Sx ma fr usp (usp - 208) b kk x A ltac:(rewrite FRS1; left; reflexivity)
                             ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia) Hin Hx) as O end end;
             unfold MLW; cbn [outside] in O |- *; clear - O; repeat split; try exact I; lia
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | lazymatch goal with |- ?g => idtac "LOOP SIDE LEFT:" g end ]
         end. }
  idtac "M12_LOOP_APPLIED".
  (* [comment removed for export] *)
  intros ms' PO. unfold meas_loop_post in PO.
  destruct PO as (ra2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & s9' & s10' & F2 & fc2 & mq2 & wv2 & wn2 & -> & MUl & WMl & MIl2 & STl2 & CVAL2 & CNVAL2).
  unfold MLW in MUl.
  clear CVAL1 CNVALw NOBJc RO ACCn ACCa SP16 SP48 SHN.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    repeat match goal with H : stk asegs ma _ _ |- _ => clear H end;
    loop_art RT AF S1 mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; fframe_tac| exact I]]]);
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  clear MUl WMl.
  idtac "M13_LOOP_DONE".
  (* [comment removed for export] *)
(* [comment removed for export] *)
  at_cut RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
               ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                               unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
  idtac "M14_CUT".
  lazymatch goal with MUx : munch _ _ ?mc |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    obj_fwd NOBJ MUx ltac:(fun b k a Hin Ha => live_out RT AF S1 usp (usp - 208) b k a Hin Ha) end.
  idtac "M14_NOBJ".
  (* [comment removed for export] *)
  pose proof AKc1 as AK1. unfold hid in AK1. pose proof AKc2 as AK2. unfold hid in AK2. pose proof AKc3 as AK3. unfold hid in AK3.
  lazymatch type of AGF with agree_on _ _ ?mc => meas_accok_keep AK1 AGF mc; meas_accok_keep AK2 AGF mc; meas_accok_keep AK3 AGF mc end.
  idtac "M14_AK".
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  idtac "M14_REFRESH".
  lazymatch goal with A : ART RT S1 ?mc |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (ACCP1 : acc asegs mc p1 4) by (apply (accok_acc_sub RT AF S1 mc (rt_live RT Σ) (rt_frames RT Σ) p1 4 A ltac:(lia)); [ solve [live_add_tac] | solve [frames_sub_tac] | exact AK1 ]);
    assert (ACCP2 : acc asegs mc p2 4) by (apply (accok_acc_sub RT AF S1 mc (rt_live RT Σ) (rt_frames RT Σ) p2 4 A ltac:(lia)); [ solve [live_add_tac] | solve [frames_sub_tac] | exact AK2 ]);
    assert (ACCP3 : acc asegs mc p3 4) by (apply (accok_acc_sub RT AF S1 mc (rt_live RT Σ) (rt_frames RT Σ) p3 4 A ltac:(lia)); [ solve [live_add_tac] | solve [frames_sub_tac] | exact AK3 ]) end.
  idtac "M14_ACCP".
  (* [comment removed for export] *)
  walk_to AF MST [(p1, p1 + 4); (p2, p2 + 4)] [e_numaFindExtrema].
  idtac "M14_AT_EXTREMA".
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; acl_ak AKc1 | split; [intros zz Hzz; acl_ak AKc2 | exact I]])
                ltac:(fun Hx => destruct Hx as [_ HxO]; cbn [outside] in HxO |- *; tauto).
  idtac "M15_ATCALL".
  unfold hid in OWN1, OWN2, OWN3.
  lazymatch type of AGF with agree_on _ _ ?mc => lazymatch goal with MUx : munch _ _ mc |- _ =>
    obj_fwd NOBJ MUx ltac:(fun b k a Hin Ha =>
      lazymatch goal with A : ART RT S1 ?mm |- _ =>
        pose proof (own_frame_live_apart RT AF S1 mm m _ p1 4 b k A OWN1 ltac:(frames_sub_tac) Hin) as Q1;
        pose proof (own_frame_live_apart RT AF S1 mm m _ p2 4 b k A OWN2 ltac:(frames_sub_tac) Hin) as Q2 end;
      cbn [outside]; clear - Q1 Q2 Ha; repeat split; try exact I; lia) end end.
  hide OWN1. hide OWN2. hide OWN3.
  idtac "M15_NOBJ".
  lazymatch type of AGF with agree_on _ _ ?mc =>
    unfold hid in UCX;
    assert (UCXd : chain_ok mc usp (bv_unsigned s0) [RA_TOP])
      by (apply (chain_ok_keep [RA_TOP] m mc usp (bv_unsigned s0) UCX); eapply agree_sub; [exact AGF|]; intros zx Hzx; split;
          [ left; exact Hzx | cbn [outside]; repeat split; try exact I; lia ]);
    hide UCX end.
  idtac "M15_FACTS".
  (* [comment removed for export] *)
  pose proof EXTREMA as EXT. unfold numaFindExtrema_cps in EXT.
  eapply cps_seq.
  { eapply EXT with (lo := lo) (nas := na) (cap := p_h v) (arr := arr) (vals := map ival_w ks) (ras := MEAS_RAS); rt_side idtac.
    all: lazymatch goal with
         | |- freg_is _ _ _ => unfold freg_is, fa0, DELTA_W; apply freg_get_same; reflexivity
         | |- numa_obj _ _ _ _ _ _ => exact NOBJ
         | |- _ <= Z.of_nat (length _) <= _ => rewrite length_map, KLEN; lia
         | |- uctx _ _ _ _ =>
             unfold uctx, MEAS_RAS; rewrite ?unsigned_lit by ul; rewrite <- RA0;
             apply (chain_ok_push _ (usp + -192) usp (bv_unsigned ra) (bv_unsigned s0) [RA_TOP]);
               [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | rewrite RA0; unfold RA_FUZZ_MEASURE; lia | apply bv_unsigned_in_range
               | rewrite !Z_to_bv_bv_unsigned; exact FRrec2
               | exact UCXd ]
         | |- numaCreate_trace_ok _ => rewrite ?unsigned_lit by ul; exact tr_meas_extrema
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "LEFT:" g
         end. }
  idtac "M16_EXTREMA_APPLIED".
  (* [comment removed for export] *)
  after_call RT AF.
  idtac "M17_AFTERCALL".
  lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
    obj_fwd_ag NOBJ AGx ltac:(fun b k a Hin Ha => split; [right; right; left; exists b, k; split; [exact Hin| exact Ha]| exact I]) end.
  idtac "M17_NOBJ".
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia] | exact I]).
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S2 end.
  unfold numa_live in *.
  lazymatch goal with H : numa_obj (rt_live RT S2) _ ?nav ?capv ?arrv ?vdv |- _ =>
    rename H into NOBJd; set (nae := nav) in *; set (cape := capv) in *; set (arre := arrv) in *; set (vde := vdv) in * end.
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJd) as (NLENd & NCAPd & ND0 & ND16 & AD0 & AD16 & INd & INad & NNEd).
  assert (FRS2 : rt_frames RT S2 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (NOBJ2 : numa_obj (rt_live RT S2) ltac:(lazymatch type of NOBJ with numa_obj _ ?mb _ _ _ _ => exact mb end) na (p_h v) arr (map ival_w ks))
    by (apply (numa_obj_mono (rt_live RT S1)); [ solve [live_add_tac] | exact NOBJ ]).
  clear NOBJ. rename NOBJ2 into NOBJ.
  idtac "M17_FACTS".
  (* [comment removed for export] *)
  chunk_facts RT AF GP nae 32. chunk_facts RT AF GP arre (4 * cape).
  fframe_chunk RT AF fr 1%nat 128 nae 32. fframe_chunk RT AF fr 1%nat 128 arre (4 * cape).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc.
  refresh RT AF. park_disj.
  lazymatch goal with A : ART RT S2 ?mc |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (ACCP3 : acc asegs mc p3 4) by (apply (accok_acc_sub RT AF S2 mc (rt_live RT Σ) (rt_frames RT Σ) p3 4 A ltac:(lia)); [ solve [live_add_tac] | solve [frames_sub_tac] | exact AK3 ]) end.
  idtac "M18_FACTS".
  walk_to AF MST [(usp - 208, usp); (fr + 96, fr + 104); (p3, p3 + 4)] [e_numaGetCount].
  idtac "M18_AT_COUNT".
  pose proof NOBJd as NOBJdc.
  lazymatch goal with MUx : munch _ _ ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    obj_fwd NOBJdc MUx ltac:(fun b k a Hin Ha =>
      lazymatch goal with A : ART RT S2 ?mm |- _ =>
        pose proof (own_frame_live_apart RT AF S2 mm m _ p3 4 b k A ltac:(unfold hid in OWN3; exact OWN3) ltac:(frames_sub_tac) Hin) as Q3;
        pose proof (live_outside_frame1 RT AF S2 mm fr usp (usp - 208) b k (bv_unsigned a) A ltac:(rewrite FRS2; left; reflexivity)
                      ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia) Hin Ha) as O end;
      cbn [outside] in O |- *; clear - O Q3 Ha; repeat split; try exact I; lia) end.
  idtac "M18_NOBJD".
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      eapply (numaGetCount_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -192) lo (rt_live RT S2) nae cape arre vde) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJdc
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | lazymatch goal with |- ?g => idtac "COUNT SIDE LEFT:" g end ]
         end. }
  idtac "M18_COUNT_APPLIED".
  (* [comment removed for export] *)
  intros ms' PO. unfold numaGetCount_post in PO.
  destruct PO as (c1' & c2' & mq3 & -> & MUl & WMl & MIl3 & STl3).
  clear NOBJdc.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    repeat match goal with H : stk asegs ma _ _ |- _ => clear H end;
    loop_art RT AF S2 mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; acl_ak AKc3 | exact I]]]);
    lazymatch goal with ACCx : acc asegs ma p3 4 |- _ =>
      acc_fwd ACCx MUl ltac:(repeat split; try exact I; first [tlia | Z.div_mod_to_equations; lia]); park ACCx; rename ACCx into ACCP3k end;
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  clear MUl WMl. unpark ACCP3k.
  fix_ret_pc.
  idtac "M19_COUNT_DONE".
  (* [comment removed for export] *)
  awalk [e_numaDestroy].
  idtac "M19_AT_NDESTROY".
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; acl_ak AKc3 | exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
  idtac "M20_ATCALL".
  (* [comment removed for export] *)
  pose proof AKc1 as AK1. unfold hid in AK1. pose proof AKc2 as AK2. unfold hid in AK2. pose proof AKc3 as AK3. unfold hid in AK3.
  lazymatch type of AGF with agree_on _ _ ?mc => meas_accok_keep AK1 AGF mc; meas_accok_keep AK2 AGF mc; meas_accok_keep AK3 AGF mc end.
  unfold hid in OWN3.
  lazymatch type of AGF with agree_on _ _ ?mc => lazymatch goal with MUx : munch _ _ mc |- _ =>
    obj_fwd NOBJd MUx ltac:(fun b k a Hin Ha =>
      lazymatch goal with A : ART RT S2 ?mm |- _ =>
        pose proof (own_frame_live_apart RT AF S2 mm m _ p3 4 b k A OWN3 ltac:(frames_sub_tac) Hin) as Q3;
        pose proof (live_outside_frame1 RT AF S2 mm fr usp (usp - 208) b k (bv_unsigned a) A ltac:(rewrite FRS2; left; reflexivity)
                      ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia) Hin Ha) as O end;
      cbn [outside] in O |- *; clear - O Q3 Ha; repeat split; try exact I; lia);
    obj_fwd NOBJ MUx ltac:(fun b k a Hin Ha =>
      lazymatch goal with A : ART RT S2 ?mm |- _ =>
        pose proof (own_frame_live_apart RT AF S2 mm m _ p3 4 b k A OWN3 ltac:(frames_sub_tac) Hin) as Q3;
        pose proof (live_outside_frame1 RT AF S2 mm fr usp (usp - 208) b k (bv_unsigned a) A ltac:(rewrite FRS2; left; reflexivity)
                      ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia) Hin Ha) as O end;
      cbn [outside] in O |- *; clear - O Q3 Ha; repeat split; try exact I; lia) end end.
  hide OWN3.
  idtac "M20_NOBJ".
  (* [comment removed for export] *)
  split_at FRV4 1%nat PNAEc. split_at PNAEc 1%nat FRV5.
  pose proof FSH as SHc. split_at SHc 12%nat SB12. split_at SB12 1%nat SB12r. clear SHc SB12r.
  idtac "M20_SLOT".
  pose proof NDESTROY as ND. unfold numaDestroy_cps in ND.
  eapply cps_seq;
    [ eapply ND with (lo := lo) (pna := fr + 96) (na := nae) (cap := cape) (arr := arre) (vals := vde); rt_side idtac;
      lazymatch goal with
         | |- optrF _ _ _ _ 8 =>
             unfold optrF, own_frame; split;
             [ exists fr, 1%nat; rewrite FRS2; change (fs_size 1) with 128;
               split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [lia|]; split; [pose proof (af_sp0_range RT AF Σ m ART0) as SPR; clear - FRHI SPR; unfold USTACK_TOP, STACK_WIN, SEGTOP_A in *; lia|]; change (ushadow 8) with [Z_to_bv 8 0];
               replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
               destruct SB12 as [[_ B] _]; exact B
             | unpark FRSH; unfold SEGTOP_A in *; clear - FR64 FR0 FRSH FRSEG; repeat split; first [lia | Z.div_mod_to_equations; lia] ]
         | |- rw_cells _ _ _ [C8 _] => exact PNAEc
         | |- numa_obj _ _ _ _ _ _ => exact NOBJd
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "ND1 LEFT:" g
         end
    | ].
  idtac "M20_ND_APPLIED".
  (* [comment removed for export] *)
  meas_after_call RT AF ltac:(idtac;
    lazymatch goal with H : rt_live RT ?S3 = numa_gone nae arre (rt_live RT S2), A : ART RT S2 ?mm |- _ =>
      rewrite (numa_gone_live RT AF S2 mm nae cape arre (rt_live RT S1) A) in H;
      [ | repeat match goal with E : rt_live RT _ = _ |- _ => rewrite E end; reflexivity | lia
      | let pp := fresh "pp" in let nn := fresh "nn" in let Hpn := fresh "Hpn" in
        intros pp nn Hpn; revert Hpn; repeat match goal with E : rt_live RT _ = _ |- _ => rewrite E end; intros Hpn; cbn [In] in Hpn;
        destruct Hpn as [Hpn|[Hpn|Hpn]]; [injection Hpn as <- <-; lia | injection Hpn as <- <-; lia | exact (LVP pp nn Hpn)] ] end).
  idtac "M21_AFTERCALL".
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S3 end.
  (* [comment removed for export] *)
  assert (NOBJs : numa_obj [(arr, 4 * p_h v); (na, 32)] ltac:(lazymatch type of NOBJ with numa_obj _ ?mb _ _ _ _ => exact mb end) na (p_h v) arr (map ival_w ks)).
  { destruct NOBJ as (NQ1 & NQ2 & (_ & NQ3) & (_ & NQ4) & NQ5).
    exact (conj NQ1 (conj NQ2 (conj (conj (or_intror (or_introl eq_refl)) NQ3) (conj (conj (or_introl eq_refl) NQ4) NQ5)))). }
  clear NOBJ.
  lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
    obj_fwd_ag NOBJs AGx ltac:(fun b k a Hin Ha =>
      cbn [In] in Hin; destruct Hin as [Hin|[Hin|Hin]]; [ injection Hin as <- <- | injection Hin as <- <- | destruct Hin ];
      (split; [ right; right; left;
                first [ exists arr, (4 * p_h v); split; [ solve [in_live_tac] | exact Ha ]
                      | exists na, 32; split; [ solve [in_live_tac] | exact Ha ] ]
              | cbn [outside]; unfold parked in *; clear - Ha FCD0 FCD1; repeat split; try exact I; lia ])) end.
  assert (NOBJ : numa_obj (rt_live RT S3) ltac:(lazymatch type of NOBJs with numa_obj _ ?mb _ _ _ _ => exact mb end) na (p_h v) arr (map ival_w ks)).
  { apply (numa_obj_mono [(arr, 4 * p_h v); (na, 32)]); [| exact NOBJs].
    intros e He. repeat match goal with E : rt_live RT _ = _ |- _ => rewrite E end. cbn [In] in He |- *. tauto. }
  clear NOBJs.
  idtac "M21_NOBJ".
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; repeat split; try exact I; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  idtac "M21_DONE".
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 208, usp)] [e_numaDestroy].
  idtac "M22_AT_NDESTROY".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  idtac "M22_ATCALL".
  (* [comment removed for export] *)
  lazymatch type of AGF with agree_on _ _ ?mc => lazymatch goal with MUx : munch _ _ mc |- _ =>
    obj_fwd NOBJ MUx ltac:(fun b k a Hin Ha => live_out RT AF S3 usp (usp - 208) b k a Hin Ha) end end.
  idtac "M22_NOBJ".
  split_at PNAc 1%nat FRV6.
  pose proof FSH as SHc. split_at SHc 8%nat SB8. split_at SB8 1%nat SB8r. clear SHc SB8r.
  idtac "M22_SLOT".
  pose proof NDESTROY as ND2. unfold numaDestroy_cps in ND2.
  eapply cps_seq;
    [ eapply ND2 with (lo := lo) (pna := fr + 64) (na := na) (cap := p_h v) (arr := arr) (vals := map ival_w ks); rt_side idtac;
      lazymatch goal with
         | |- optrF _ _ _ _ 8 =>
             unfold optrF, own_frame; split;
             [ exists fr, 1%nat; rewrite FRS3; change (fs_size 1) with 128;
               split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [lia|]; split; [pose proof (af_sp0_range RT AF Σ m ART0) as SPR; clear - FRHI SPR; unfold USTACK_TOP, STACK_WIN, SEGTOP_A in *; lia|]; change (ushadow 8) with [Z_to_bv 8 0];
               replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
               destruct SB8 as [[_ B] _]; exact B
             | unpark FRSH; unfold SEGTOP_A in *; clear - FR64 FR0 FRSH FRSEG; repeat split; first [lia | Z.div_mod_to_equations; lia] ]
         | |- rw_cells _ _ _ [C8 _] => exact PNAc
         | |- numa_obj _ _ _ _ _ _ => exact NOBJ
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "ND2 LEFT:" g
         end
    | ].
  idtac "M22_ND_APPLIED".
  meas_after_call RT AF ltac:(idtac;
    lazymatch goal with H : rt_live RT ?S4 = numa_gone na arr (rt_live RT S3), A : ART RT S3 ?mm |- _ =>
      rewrite (numa_gone_live RT AF S3 mm na (p_h v) arr (rt_live RT Σ) A) in H;
      [ | repeat match goal with E : rt_live RT _ = _ |- _ => rewrite E end; reflexivity | lia
      | let pp := fresh "pp" in let nn := fresh "nn" in let Hpn := fresh "Hpn" in
        intros pp nn Hpn; exact (LVP pp nn Hpn) ] end).
  idtac "M22_AFTERCALL".
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S4 end.
  clear NOBJ.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; repeat split; try exact I; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  idtac "M22_DONE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  repeat match goal with H : rw_cells asegs _ (fr + _) _ |- _ => clear H end.
  repeat match goal with H : rw_cells asegs _ (fr / 8 + _) [C1 _] |- _ => clear H end.
  repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
  clear_acc. clear AK1 AK2 AK3 PXC NOBJd.
  park CP1. park CP2. park CP3.
  walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x12127c].
  idtac "M23_AT_FLAG".
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    unpark_cells_munch CP1 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p1 4 _ AKc1 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    unpark_cells_munch CP2 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p2 4 _ AKc2 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    unpark_cells_munch CP3 MUx
        ltac:(fun Hx => let Ha := fresh "Ha" in pose proof (accok_aclient _ _ _ usp p3 4 _ AKc3 Hx) as Ha;
                        pose proof (PFS0 _ Ha); destruct (NFA0 _ Ha) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  frame_release_w RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x121284
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact (proj1 Hx))
      ltac:(fun fl FLN =>
              assert (FLP1 : fl < p1 \/ p1 + 4 <= fl)
                by (destruct (Z_lt_ge_dec fl p1) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (p1 + 4)) as [FG2|]; [| right; lia]; exfalso; apply FLN;
                    apply (aclient_mono _ _ 140737488355328 _ _ _ _ (accok_aclient _ _ _ 140737488355328 p1 4 fl AKc1 ltac:(lia)));
                    [solve [live_sub_tac] | solve [frames_sub_tac] | ul]);
              assert (FLP2 : fl < p2 \/ p2 + 4 <= fl)
                by (destruct (Z_lt_ge_dec fl p2) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (p2 + 4)) as [FG2|]; [| right; lia]; exfalso; apply FLN;
                    apply (aclient_mono _ _ 140737488355328 _ _ _ _ (accok_aclient _ _ _ 140737488355328 p2 4 fl AKc2 ltac:(lia)));
                    [solve [live_sub_tac] | solve [frames_sub_tac] | ul]);
              assert (FLP3 : fl < p3 \/ p3 + 4 <= fl)
                by (destruct (Z_lt_ge_dec fl p3) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (p3 + 4)) as [FG2|]; [| right; lia]; exfalso; apply FLN;
                    apply (aclient_mono _ _ 140737488355328 _ _ _ _ (accok_aclient _ _ _ 140737488355328 p3 4 fl AKc3 ltac:(lia)));
                    [solve [live_sub_tac] | solve [frames_sub_tac] | ul])).
  idtac "M23_RELEASED".
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  rewrite ?ESP.
  walk_to AF MST [(usp - 208, usp)] (@nil Z).
  (* [comment removed for export] *)
  idtac "M23_AT_RET".
  cps_stop.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  lazymatch type of CP1 with rw_cells _ _ _ [C4 ?y] => eexists; exists y end.
  lazymatch type of CP2 with rw_cells _ _ _ [C4 ?y] => exists y end.
  lazymatch type of CP3 with rw_cells _ _ _ [C4 ?y] => exists y end.
  split; [| alg_tac].
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; assumption] | split; assumption]|].
  split.
  { intros a Ha Ho. apply AGF. split; [| exact Ho].
    revert Ha. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. intros Ha. exact Ha. }
  split; [exact CP1 | split; [exact CP2 | exact CP3]].
Qed.
End MEAS.
