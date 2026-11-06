(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Wf_nat.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m U_Pahif.

Module U_Paczw.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m U_Pahif ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma dispatch_ok : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A m -> ainv A m md ->
    evt rsegs (fun ms' => ms' = disp_ms E x ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 m)
        (head_ms E x ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 m).
  Proof.
    intros until t6. intros PE PI AINV.
    open_pinv PI. (first [ dand4 VEPO as LVEP VEPC TAG PADS | destruct VEPO as (LVEP & VEPC & TAG & PADS) ]).
    (first [ dex4 FRAME as j0 j8 j16 j24; rename FRAME into FR | dand5 FRAME as j0 j8 j16 j24 FR | destruct FRAME as (j0 & j8 & j16 & j24 & FR) ]). (first [ dand3 DATA as LDATA DBY DLEN | destruct DATA as (LDATA & DBY & DLEN) ]).
    (first [ pose proof ((live_geom LayoutPU A m md _ _ AINV LVEP)) as dR_4; dand5 dR_4 as _ _ VEPlo VEPhi _ | destruct (live_geom LayoutPU A m md _ _ AINV LVEP) as (_ & _ & VEPlo & VEPhi & _) ]).
    (first [ pose proof ((live_geom LayoutPU A m md _ _ AINV LDATA)) as dR_5; dand5 dR_5 as _ _ Dlo Dhi _ | destruct (live_geom LayoutPU A m md _ _ AINV LDATA) as (_ & _ & Dlo & Dhi & _) ]).
    (first [ dand6 PE as HG FL NN CEIL LOP _ | destruct PE as (HG & FL & NN & CEIL & LOP & _) ]). (first [ dand3 HG as G1 G2 G3 | destruct HG as (G1 & G2 & G3) ]).
    pose proof alloc_ceiling_val as CV. unfold pe_e, pe_N, NMAX in *. unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK in LOP.
    pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size _ _ _ TAG PADS) in VEPB.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. rewrite pframe_size in FRB.
    (first [ dand7 PADS as P36 P124 P140 P196 P236 P268 P308 | destruct PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC. unfold pframe in FR. rewrite STATE in VEPC. fold_al_segs.
    unfold head_ms, disp_ms, loop_ms, lms, PC_HEAD, pe_sp in *.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K.
    { exfalso. revert K. destruct (x_st x); vm_compute; lia. }
    clear K.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K. { exfalso. unsign K. lia. } clear K.
    (* [comment removed for export] *)
    assert (CR : 0 <= stU (x_st x) < 2^64) by (clear; destruct (x_st x); cbn; lia).
    set (c := stU (x_st x)) in *. cbn [stU]. cbn [stU] in FR.
    clear - MI FR FRB CR c.
    repeat (zstep;
      try (let K := fresh "K" in
           if_cases K; zify_cond K; try rewrite (Z.mod_small c 18446744073709551616 CR) in K;
           first
           [ (* [comment removed for export] *)
             lazymatch type of K with c = _ =>
               subst c; destruct (x_st x); cbn [stU] in K;
               first [ discriminate K | clear K; cbn [stU disp_pc disp_a1 disp_a2 disp_s8 oreg]; finish ] end
           | (* [comment removed for export] *)
             lazymatch goal with
             | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1b068) _ _ _ _) =>
                 exfalso; subst c; destruct (x_st x); cbn [stU] in *;
                 match goal with H : ?a <> ?a |- _ => exact (H eq_refl) end
             | _ => idtac
             end ])).
  Qed.
End S.
End U_Paczw.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_La7nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Cov8m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Pahbe.U_Paczw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  (* [comment removed for export] *)
  Lemma hstep_trans : forall E x x1 x2 A A1 A2 m m1 m2,
    hstep E x x1 A A1 m m1 -> hstep E x1 x2 A1 A2 m1 m2 -> hstep E x x2 A A2 m m2.
  Proof.
    (intros E x x1 x2 A A1 A2 m m1 m2; (first [ intro dR_4; dand3 dR_4 as L1 N1 C1 | intros (L1 & N1 & C1) ]); (first [ intro dR_5; dand3 dR_5 as L2 N2 C2 | intros (L2 & N2 & C2) ])).
    split; [|split].
    - intros p k Hp NB. apply L2; [apply L1; assumption|].
      intros B1. destruct (N1 p B1) as [B|B]; [exact (NB B)| congruence].
    - intros p B2. destruct (N2 p B2) as [B1|D1]; [exact (N1 p B1)|].
      destruct (Classical_Prop.classic (pst_blocks x p)) as [B|NB]; [left; exact B| right].
      destruct (a_live A p) as [k|] eqn:AL; [|reflexivity]. exfalso. rewrite (L1 p k AL NB) in D1. discriminate D1.
    - (first [ dand3 C2 as D1 D2 D3 | destruct C2 as (D1 & D2 & D3) ]).
      eapply (cframe_seq LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ _ m m1 m2 C1 (conj D1 (conj D2 D3))); [lia| lia| exact D2| intros a X; exact X| |].
      + (* [comment removed for export] *)
        intros a Z1. unfold pzone in Z1. unfold parse_new. cbn [option_map].
        destruct Z1 as [Z1|[Z1|[Z1|[Z1|[Z1|Z1]]]]].
        * right. unfold pzone. left; exact Z1.
        * right. unfold pzone. right; left; exact Z1.
        * left. left. exact Z1.
        * left. right; left. destruct (x_va x1); [exact Z1| destruct Z1].
        * left. right; right. destruct (x_vi x1); [exact Z1| destruct Z1].
        * right. unfold pzone. right; right; right; right; right. exact Z1.
      + intros a X. right; left; exact X.
  Qed.

  (* [comment removed for export] *)
  Hypothesis HND : forall st, st <> S_MatchBuf -> handler_stmt st.

  (* [comment removed for export] *)
  Lemma loop_ok : forall (n : nat) (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
    (Z.to_nat (phi E x) < n)%nat ->
    penv_ok E -> pinv E x A m -> ainv A m md -> x_st x <> S_MatchBuf -> x_p x < pe_e E ->
    exit_K E x A m md T ->
    realizes rsegs (mkCfg (head_ms E x ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 m) md) T.
  Proof.
    induction n as [|n IH]; intros until t6; intros PHI PE PI AINV NMB PLT KX; [exfalso; lia|]. unfold exit_K in KX.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    (* [comment removed for export] *)
    eapply rz_evt; [eapply (dispatch_ok E x A m md); eassumption| exact MDH| exact MDL|].
    intros ms' ->.
    (* [comment removed for export] *)
    apply (HND (x_st x) NMB E x A m md T); [exact PE| exact PI| exact AINV| reflexivity| exact PLT| |exact KX].
    unfold latch_K.
    (* [comment removed for export] *)
    intros x' A' m' md' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' PI' AINV' MDF HS DEC.
    pose proof (as_lazy_nil A' m' md' AINV') as [MDL' MDH'].
    pose proof (pi_pe _ _ _ _ PI') as PLE'. pose proof (pi_verp _ _ _ _ PI') as VERP'. (first [ pose proof ((pi_data _ _ _ _ PI')) as dR_2; dand3 dR_2 as LD _ DLEN | pose proof (pi_data _ _ _ _ PI') as (LD & _ & DLEN) ]).
    (first [ pose proof ((live_geom LayoutPU A' m' md' _ _ AINV' LD)) as dR_3; dand5 dR_3 as _ _ Dlo Dhi _ | destruct (live_geom LayoutPU A' m' md' _ _ AINV' LD) as (_ & _ & Dlo & Dhi & _) ]).
    pose proof alloc_ceiling_val as CV.
    assert (EE : 0 <= pe_e E <= alloc_ceiling) by (unfold pe_e, pe_N; lia).
    assert (XP : 0 <= x_p x' < 2^64) by lia.
    unfold latch_ms, loop_ms, lms, PC_LATCH.
    apply rz_go; [exact MDH'| exact MDL'|].
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      unsign K. destruct (DEC ltac:(lia)) as [PHI' NMB'].
      apply rz_stop. change (Z_to_bv 64 0x1a1c0) with (Z_to_bv 64 PC_HEAD).
      apply (IH E x' A' m' md' T); [ pose proof (rank_bound E x); pose proof (rank_bound E x'); unfold phi in *; lia
        | exact PE| exact PI'| exact AINV'| exact NMB'| lia|].
      (* [comment removed for export] *)
      intros x'' A'' m'' md'' ra'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s1'' s7'' t3'' t4'' t5'' t6'' PI'' AINV'' MDF' HS' PEQ.
      apply (KX x'' A'' m'' md''); [exact PI''| exact AINV''| eapply md_frame_trans; [exact MDF| exact MDF']| eapply hstep_trans; [exact HS| exact HS']| exact PEQ].
    - (* [comment removed for export] *)
      unsign K. zstep. apply rz_stop.
      apply (KX x' A' m' md'); [exact PI'| exact AINV'| exact MDF| exact HS| lia].
  Qed.
End S.
