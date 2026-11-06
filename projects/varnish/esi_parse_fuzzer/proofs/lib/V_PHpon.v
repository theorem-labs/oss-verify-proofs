(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_Pa4g6 V_VS6ai V_PH51p Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Pa4g6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VS6ai OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  (* [comment removed for export] *)
  Lemma world_keep : forall E x A A' m m' md win N,
    penv_ok E -> pinv E x A m -> ainv A m md ->
    cframe LayoutP0 (owned A) (owned A') (pe_sp E) win nowhere N m m' ->
    alloc_ceiling <= pe_sp E - win -> 0 <= win ->
    (forall p k, a_live A p = Some k -> a_live A' p = Some k) ->
       vep_obj LayoutP0 A' m' (pe_VEP E) (x_v x) (x_tag x) (x_q x)
    /\ vsb_obj LayoutP0 A' m' (pe_S E) (x_vv x) false
    /\ a_live A' (pe_wa E) = Some 40
    /\ va_world E x A' m' /\ vi_world E x A' m'
    /\ data_obj LayoutP0 A' m' (pe_DATA E) (pe_inp E)
    /\ henv_ok LayoutP0 VI0 (pe_H E) m' /\ img_ok0 m'
    /\ (exists j0 j8, rw_cells rsegs m' (pe_sp E) (pframe E j0 j8)).
  Proof.
    intros E x A A' m m' md win N PE PI AINV CF CEIL WPOS LK.
    pose proof PE as ((G1 & G2 & G3) & _).
    pose proof (conj G1 (conj G2 G3) : henv_geom _) as HG.
    assert (SPH : pe_sp E <= h_sp (pe_H E)) by (unfold pe_sp; lia).
    assert (CV : forall excl, vcover (pe_H E) A excl nowhere) by (intros excl a Ha; destruct Ha).
    assert (HC : forall excl, hcover A excl nowhere) by (intros excl a Ha; destruct Ha).
    destruct PI as [VEPO BASE FLG VSBF STUP STATE CNT VERP PLE B01 TAGI DELIM ESIC UNTL MTCH DOST ARMED ATTR ATTRST
                    MATTR LOOKA LOOKM VSBO ROOM OUT APART WAL AVSB VA VI DATA HENV IMG STK FRAME MI LB NL].
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    - eapply (vep_obj_call (pe_H E) A A' m m' md (pe_sp E) win nowhere N [pe_VEP E] AINV CF HG CEIL);
        [apply CV| left; reflexivity| apply LK; exact (proj1 VEPO)| exact VEPO].
    - eapply (vsb_obj_call (pe_H E) A A' m m' md (pe_sp E) win nowhere N [pe_S E; vb_buf (x_vv x)] AINV CF HG CEIL);
        [apply CV| left; reflexivity| right; left; reflexivity
        | apply LK; exact (proj1 (proj2 (proj2 VSBO)))| apply LK; exact (proj1 (proj2 (proj2 (proj2 VSBO))))| exact VSBO].
    - apply LK. exact WAL.
    - unfold va_world in *. destruct (x_va x) as [y|]; [| exact VA].
      (first [ dand4 VA as Q1 Q2 Q3 Q4 | destruct VA as (Q1 & Q2 & Q3 & Q4) ]). refine (conj Q1 (conj _ (conj Q3 Q4))).
      eapply (vsb_obj_call (pe_H E) A A' m m' md (pe_sp E) win nowhere N [x_v x Fattr_vsb; vb_buf y] AINV CF HG CEIL);
        [apply CV| left; reflexivity| right; left; reflexivity
        | apply LK; exact (proj1 (proj2 (proj2 Q2)))| apply LK; exact (proj1 (proj2 (proj2 (proj2 Q2))))| exact Q2].
    - unfold vi_world in *. destruct (x_vi x) as [y|]; [| exact VI].
      (first [ dand3 VI as Q1 Q2 Q3 | destruct VI as (Q1 & Q2 & Q3) ]). refine (conj Q1 (conj _ Q3)).
      eapply (vsb_obj_call (pe_H E) A A' m m' md (pe_sp E) win nowhere N [x_v x Finclude_src; vb_buf y] AINV CF HG CEIL);
        [apply CV| left; reflexivity| right; left; reflexivity
        | apply LK; exact (proj1 (proj2 (proj2 Q2)))| apply LK; exact (proj1 (proj2 (proj2 (proj2 Q2))))| exact Q2].
    - eapply (data_obj_call (pe_H E) A A' m m' md (pe_sp E) win nowhere N [pe_DATA E] AINV CF HG CEIL);
        [apply CV| left; reflexivity| apply LK; exact (proj1 DATA)| exact DATA].
    - eapply (henv_call (pe_H E) A A' m m' md (pe_sp E) win nowhere N [] AINV CF HG CEIL SPH); [apply HC| exact HENV].
    - eapply (img_call (pe_H E) A A' m m' md (pe_sp E) win nowhere N [] AINV CF HG CEIL); [apply CV| exact IMG].
    - (first [ dex2 FRAME as j0 j8; rename FRAME into FR | dand3 FRAME as j0 j8 FR | destruct FRAME as (j0 & j8 & FR) ]). exists j0, j8.
      eapply (pframe_call E A A' m m' md (pe_sp E) win nowhere N []); [exact PE| exact AINV| exact CF| exact CEIL| exact WPOS| lia| apply CV| exact FR].
  Qed.

  Lemma PH_AttrGetValue : handler_stmt S_AttrGetValue.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    pose proof PI as PI0.
    (* [comment removed for export] *)
    (first [ pose proof ((pinv_sizes _ _ _ _ PI)) as dR_s; dand4 dR_s as OUT7 WBB LEN0 SZ0 | pose proof (pinv_sizes _ _ _ _ PI) as (OUT7 & WBB & LEN0 & SZ0) ]).
    handler_prologue PE PI AINV ST.
    assert (AV0 : x_v x Fattr_vsb = 0).
    { destruct (Z.eq_dec (x_v x Fattr_vsb) 0) as [X|X]; [exact X| exfalso; exact (AVSB X)]. }
    assert (EVA : x_va x = None).
    { revert VA AV0. clear. destruct (x_va x); [| reflexivity]. intros VA AV0. exfalso. exact (proj1 VA AV0). }
    assert (WNL2 : 0 <= pw_nlive (x_va x) (x_vi x) <= 2) by (rewrite EVA; unfold pw_nlive; clear; destruct (x_vi x); lia).
    assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. zstep. rewrite AV0. zstep. if_cases K1; zify_cond K1. { dead K1. } clear K1.
    zstep. apply rz_stop.
    eapply VSB_new_auto_cps;
      [ exact AINV | exact MI | exists (pe_VEP E), 312; exact LVEP
      | revert LB BUDL WBB NN; unfold PARSE_LIVE, pe_N; clear; intros; lia
      | revert NL BUDN WNL2; unfold PARSE_NLIVE; clear; intros; lia
      | reflexivity
      | rewrite unsigned_lit by exact SPR; rewrite PSP, Zminus_mod, G1; reflexivity
      | rewrite unsigned_lit by (clear; lia); reflexivity
      | rewrite unsigned_lit by exact SPR; exact STK
      | exact CEIL
      | rewrite unsigned_lit by exact SPR; revert LOP PSP; clear; unfold NEWAUTO_STACK; unfold_stacks_g; intros; lia
      | rewrite unsigned_lit by exact SPR; rewrite PSP; clear - G3; unfold HFRAME in G3; lia | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' AINV' MI' MDF STK' RES.
    rewrite unsigned_lit in STK', RES by exact SPR.
    replace (ret_pc (Z_to_bv 64 0x1a828)) with (Z_to_bv 64 0x1a828) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
    assert (WIN : alloc_ceiling <= pe_sp E - NEWAUTO_STACK) by (revert LOP PSP CEIL; clear; unfold NEWAUTO_STACK; unfold_stacks_g; intros; lia).
    assert (WPOS : 0 <= NEWAUTO_STACK) by (unfold NEWAUTO_STACK; unfold_stacks_g; clear; lia).
    (* [comment removed for export] *)
    destruct RES as (b & RNZ & VSO & FRr & FRb & LQ & LBn & NLn & CF).
    assert (LK : forall p k, a_live A p = Some k -> a_live A' p = Some k).
    { intros p k Hp. rewrite LQ; [exact Hp| intros ->; congruence| intros ->; congruence]. }
    destruct (world_keep E x A A' m m' md _ _ PE PI0 AINV CF WIN WPOS LK)
      as (VEPO1 & VSBO1 & WAL1 & VA1 & VI1 & DATA1 & HENV1 & IMG1 & (j0' & j8' & FR1)).
    (* [comment removed for export] *)
    assert (NEW : forall p k, a_live A p = Some k -> p <> r /\ p <> b) by (intros p k Hp; split; intros ->; congruence).
    pose proof (NEW _ _ LVEP) as [NrV NbV]. pose proof (NEW _ _ WAL) as [NrW NbW]. pose proof (NEW _ _ LDATA) as [NrD NbD].
    pose proof (NEW _ _ LVS) as [NrS NbS]. pose proof (NEW _ _ LVB) as [NrB NbB].
    assert (NI : match x_vi x with None => True | Some y => (x_v x Finclude_src <> r /\ x_v x Finclude_src <> b) /\ (vb_buf y <> r /\ vb_buf y <> b) end).
    { clear - VI NEW. destruct (x_vi x) as [yi|]; [| exact I]. (first [ dand3 VI as _ (_ & _ & L1 & L2 & _) _ | destruct VI as (_ & (_ & _ & L1 & L2 & _) & _) ]).
      split; [exact (NEW _ _ L1)| exact (NEW _ _ L2)]. }
    (first [ pose proof (VSO) as dR_6; dand6 dR_6 as _ _ Lr Lb Nrb _ | pose proof VSO as (_ & _ & Lr & Lb & Nrb & _) ]). cbn [vb_buf vb_size vsb_fresh] in Lb, Nrb.
    (* [comment removed for export] *)
    set (xm := PST (x_p x) S_AttrGetValue (fupd (x_v x) Fattr_vsb r) (x_tag x) (x_q x) (x_vv x) (Some (vsb_fresh b)) (x_vi x)).
    assert (HS1 : hstep E x xm A A' m m').
    { eapply (hstep_intro E x xm A A' m m' PARSE_STACK nowhere (fun a => blk r 40 a \/ blk b 16 a)).
      - eapply cframe_rebase; [exact CF| revert WIN; clear; unfold NEWAUTO_STACK; unfold_stacks_g; intros; lia| eapply parse_window_mapped; [exact PE| exact STK'| exact FR1]].
      - clear; lia.
      - eapply parse_window_mapped; [exact PE| exact STK'| exact FR1].
      - intros a Ha; destruct Ha.
      - subst xm. unfold parse_new, pzone. cbn [x_v x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb]. unfold vsb_blocks. cbn [vb_buf vb_size vsb_fresh].
        intros a [Ha|[[Ha|Ha]|Ha]]; [right; right; right; left; exact Ha| left; left; exact Ha| left; right; exact Ha| right; right; right; right; right; left].
        destruct (x_vi x) as [yi|]; [exact Ha| destruct Ha].
      - intros p k Hp _. exact (LK p k Hp).
      - subst xm. unfold pst_blocks. cbn [x_v x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb vb_buf vsb_fresh]. rewrite EVA.
        intros p [Hp|[[Hp|Hp]|Hp]]; [left; left; exact Hp| right; rewrite Hp; exact FRr| right; rewrite Hp; exact FRb| left; right; right; exact Hp]. }
    (* [comment removed for export] *)
    rename LB into LBo. rename NL into NLo.
    clear VEPC FR STK MI HENV IMG VSBO DATA DBY DLEN LDATA VA VI WAL LVEP LVS LVB AINV PI0 NEW LK CF j0 j8 FRB VEPB.
    (first [ dand4 VEPO1 as LVEP VEPC TAG' PADS' | destruct VEPO1 as (LVEP & VEPC & TAG' & PADS') ]). clear TAG' PADS'.
    unfold vep_cells in VEPC. rewrite STATE in VEPC. fold_al_segs.
    rename FR1 into FR. unfold pframe in FR. rename STK' into STK. rename MI' into MI.
    rename VSBO1 into VSBO. rename WAL1 into WAL. rename DATA1 into DATA. rename HENV1 into HENV. rename IMG1 into IMG.
    rename VA1 into VA. rename VI1 into VI. unfold va_world in VA. unfold vi_world in VI.
    pose proof (proj1 (proj2 (proj2 VSBO))) as LVS. pose proof (proj1 (proj2 (proj2 (proj2 VSBO)))) as LVB.
    pose proof DATA as (LDATA & DBY & DLEN).
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m') as MU. pose proof (wmono_refl rsegs m') as WM.
    assert (WZ : wzone E A' [pe_S E; vb_buf (x_vv x); pe_DATA E; r; b; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH'| exact MDL'|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply (KL (PST (x_p x) S_AttrDelim (fupd (fupd (x_v x) Fattr_vsb r) Fstate (st0 S_AttrDelim))
                    (x_tag x) (x_q x) (x_vv x) (Some (vsb_fresh b)) (x_vi x)) A' _ md').
    2:{ eapply (ainv_stores E A' m' _ md' _ _ PE0 AINV' MU WM WZ). }
    2:{ exact MDF. }
    2:{ eapply hstep_trans; [exact HS1|].
        eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same xm _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E xm _ a _ _ X); reflexivity ].
        subst xm. w_in_zone_tac. left. unfold blk. lia. }
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
    + (* [comment removed for export] *) intros _ _. exact (ATTRST I (or_introl eq_refl)).
    + (* [comment removed for export] *)
      revert OUT. unfold oacost, oicost. rewrite EVA. cbn [x_va x_vi x_st x_p x_vv vb_len vsb_fresh]. clear. intros; lia.
    + (* [comment removed for export] *)
      split; [exact RNZ|]. split; [eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV' MU WM WZ); [in_list| in_list| exact VSO]|].
      split; [cbn; clear; lia|].
      intros y Hy. cbn in Hy. cbn [vb_buf vsb_fresh].
      destruct Hy as [<-|[<-|[<-|[<-|[<-|[]]]]]]; split; apply not_eq_sym; assumption.
    + (* [comment removed for export] *)
      rewrite EVA in VI. revert VI NI. destruct (x_vi x) as [yi|] eqn:EVI; intros VI NI; [| exact VI].
      (first [ dand6 VI as Q1 Q2 Q3 Q3b Q4 _ | destruct VI as (Q1 & Q2 & Q3 & Q3b & Q4 & _) ]). destruct NI as [[N1 N2] [N3 N4]].
      refine (conj Q1 (conj _ (conj Q3 (conj Q3b (conj Q4 _))))).
      { eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV' MU WM WZ); [in_list| in_list| exact Q2]. }
      intros y Hy. cbn in Hy. cbn [vb_buf vsb_fresh].
      destruct Hy as [<-|[<-|[]]]; [split; [exact N1| exact N3] | split; [exact N2| exact N4]].
    + (* [comment removed for export] *)
      revert LBo LBn. rewrite EVA. clear. unfold pw_bytes. cbn [vb_size vsb_fresh]. intros; lia.
    + (* [comment removed for export] *) revert NLo NLn. rewrite EVA. clear. unfold pw_nlive. intros; lia.
  Qed.
End S.
