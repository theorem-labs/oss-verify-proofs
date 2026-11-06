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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Cells Step RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_Pa4g6 V_PH51p V_vejh3 R_strlen V_Leaves V_PD648 Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Pa4g6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vejh3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strlen OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Leaves OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PD648 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_find_some : forall es inp i, mtab_wf es -> vm_find es inp = Some i ->
  exists e, nth_error es i = Some e /\
            ((me_ptr e = 0 /\ me_str e = []) \/ (me_ptr e <> 0 /\ is_prefixb (me_str e) inp = true /\ (1 <= length (me_str e) <= 8)%nat)).
Proof.
  induction es as [|e es IH]; intros inp i WF H; cbn in H; [cbn in WF; contradiction|].
  destruct es as [|e2 es2].
  - destruct WF as [E0 Es]. rewrite E0 in H. cbn in H. injection H as <-. exists e. split; [reflexivity| left; auto].
  - destruct WF as (Hp & Hl & Hn & WF').
    destruct (me_ptr e =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]. apply Z.eqb_neq in E0.
    destruct (is_prefixb (me_str e) inp) eqn:EP.
    + injection H as <-. exists e. split; [reflexivity| right; auto].
    + destruct (runs_outb (me_str e) inp); [discriminate|].
      destruct (vm_find (e2 :: es2) inp) as [j|] eqn:EJ; [|discriminate]. cbn in H. injection H as <-.
      destruct (IH inp j WF' EJ) as (e' & Hn' & F). exists e'. split; [exact Hn'| exact F].
Qed.

Lemma vm_find_none : forall es inp, mtab_wf es -> vm_find es inp = None -> (length inp <= 7)%nat.
Proof.
  induction es as [|e es IH]; intros inp WF H; cbn in H; [discriminate|].
  destruct es as [|e2 es2].
  - destruct WF as [E0 _]. rewrite E0 in H. cbn in H. discriminate.
  - destruct WF as (Hp & Hl & Hn & WF').
    destruct (me_ptr e =? 0); [discriminate|]. destruct (is_prefixb (me_str e) inp); [discriminate|].
    destruct (runs_outb (me_str e) inp) eqn:ER.
    + apply runs_outb_length in ER. lia.
    + destruct (vm_find (e2 :: es2) inp) eqn:EJ; [discriminate|]. eapply IH; eauto.
Qed.

Lemma vm_find_lt : forall es inp i, mtab_wf es -> vm_find es inp = Some i -> (i < length es)%nat.
Proof. intros. eapply vm_find_bound; eauto. Qed.

(* [comment removed for export] *)
Definition tgt_ok (es : list mentry) (ts : list (nat * vstate)) : Prop :=
  forall i e, nth_error es i = Some e ->
    exists k S', nth_error ts i = Some (k, S') /\ me_svar e = VEPVARS0 + Z.of_nat k /\
                 cell_at vepvars0 k = Some (C8 (Z_to_bv 64 (st0 S'))) /\ me_sval e = st0 S'.

Definition tgts_bom : list (nat * vstate) := [(0%nat, S_Start); (8%nat, S_BOM)].
Definition tgts_attr_include : list (nat * vstate) := [(104%nat, S_AttrGetValue); (104%nat, S_AttrGetValue); (112%nat, S_SkipAttribute)].
Definition tgts_esi : list (nat * vstate) := [(72%nat, S_ESI_Include); (80%nat, S_ESI_Remove); (88%nat, S_ESI_Comment); (96%nat, S_ESI_Bogon)].
Definition tgts_starttag : list (nat * vstate) :=
  [(16%nat, S_CommentESI); (24%nat, S_NxtTag); (32%nat, S_Comment); (40%nat, S_end_ESITag); (48%nat, S_ESITag); (56%nat, S_CDATA); (64%nat, S_NotMyTag)].

Ltac tgt_ok_tac :=
  intros [|[|[|[|[|[|[|[|i]]]]]]]] e H; cbn in H; try discriminate; injection H as <-;
  eexists _, _; (split; [reflexivity|]); (split; [reflexivity|]); split; reflexivity.

Lemma tgt_bom : tgt_ok tbl_bom tgts_bom. Proof. tgt_ok_tac. Qed.
Lemma tgt_attr_include : tgt_ok tbl_attr_include tgts_attr_include. Proof. tgt_ok_tac. Qed.
Lemma tgt_esi : tgt_ok tbl_esi tgts_esi. Proof. tgt_ok_tac. Qed.
Lemma tgt_starttag : tgt_ok tbl_starttag tgts_starttag. Proof. tgt_ok_tac. Qed.

(* [comment removed for export] *)
Definition tab4 (Tb : Z) (es : list mentry) (ts : list (nat * vstate)) : Prop :=
  (Tb = TBL_bom /\ es = tbl_bom /\ ts = tgts_bom) \/ (Tb = TBL_attr_include /\ es = tbl_attr_include /\ ts = tgts_attr_include) \/
  (Tb = TBL_esi /\ es = tbl_esi /\ ts = tgts_esi) \/ (Tb = TBL_starttag /\ es = tbl_starttag /\ ts = tgts_starttag).

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Lemma PH_Match : handler_stmt S_Match.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E)]) by wzone_tac.
    assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
    assert (EVM : VM_FRAME = 48) by reflexivity.
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + rank E x) by reflexivity.
    (* [comment removed for export] *)
    assert (TBL : exists Tb es ts, x_v x Fmatch = Tb /\ ro_cells rsegs m Tb (mtab_cells es) /\ mtab_wf es /\ mtab_strings m es /\
                  tgt_ok es ts /\ IMG0_LO <= Tb /\ Tb + Z.of_nat (cells_size (mtab_cells es)) <= IMG0_HI /\
                  (forall i e, nth_error es i = Some e -> me_ptr e <> 0 -> 0 <= me_ptr e /\ me_ptr e + 16 <= IMG0_LO) /\ tab4 Tb es ts).
    { pose proof IMG as (_ & _ & _ & _ & _ & _ & ITb & ITa & ITe & ITs).
      destruct (MTCH eq_refl) as [TM|[TM|[TM|TM]]].
      - exists TBL_bom, tbl_bom, tgts_bom. split; [exact TM|]. split; [exact ITb|]. split; [exact tbl_bom_wf|]. split; [exact (tbl_bom_strings m MI)|].
        split; [exact tgt_bom|]. split; [unfold IMG0_LO, TBL_bom; clear; lia|]. split; [unfold IMG0_HI, TBL_bom; cbn; clear; lia|].
        split; [| left; repeat split; reflexivity].
        intros [|[|[|i]]] e H; cbn in H; try discriminate; injection H as <-; cbn; unfold IMG0_LO; clear; intros; lia.
      - exists TBL_starttag, tbl_starttag, tgts_starttag. split; [exact TM|]. split; [exact ITs|]. split; [exact tbl_starttag_wf|].
        split; [exact (tbl_starttag_strings m MI)|].
        split; [exact tgt_starttag|]. split; [unfold IMG0_LO, TBL_starttag; clear; lia|]. split; [unfold IMG0_HI, TBL_starttag; cbn; clear; lia|].
        split; [| right; right; right; repeat split; reflexivity].
        intros [|[|[|[|[|[|[|[|i]]]]]]]] e H; cbn in H; try discriminate; injection H as <-; cbn; unfold IMG0_LO; clear; intros; lia.
      - exists TBL_esi, tbl_esi, tgts_esi. split; [exact TM|]. split; [exact ITe|]. split; [exact tbl_esi_wf|]. split; [exact (tbl_esi_strings m MI)|].
        split; [exact tgt_esi|]. split; [unfold IMG0_LO, TBL_esi; clear; lia|]. split; [unfold IMG0_HI, TBL_esi; cbn; clear; lia|].
        split; [| right; right; left; repeat split; reflexivity].
        intros [|[|[|[|[|i]]]]] e H; cbn in H; try discriminate; injection H as <-; cbn; unfold IMG0_LO; clear; intros; lia.
      - exists TBL_attr_include, tbl_attr_include, tgts_attr_include. split; [exact TM|]. split; [exact ITa|]. split; [exact tbl_attr_include_wf|].
        split; [exact (tbl_attr_include_strings m MI)|].
        split; [exact tgt_attr_include|]. split; [unfold IMG0_LO, TBL_attr_include; clear; lia|]. split; [unfold IMG0_HI, TBL_attr_include; cbn; clear; lia|].
        split; [| right; left; repeat split; reflexivity].
        intros [|[|[|[|i]]]] e H; cbn in H; try discriminate; injection H as <-; cbn; unfold IMG0_LO; clear; intros; lia. }
    destruct TBL as (Tb & es & ts & TM & ITB & WF & STRS & TGT & TLO & THI & STRB & TAB4).
    (* [comment removed for export] *)
    pose proof (pd_split3 rsegs m (pe_VEP E) _ 39 (C8 (Z_to_bv 64 (x_v x Fmatch))) VEPC eq_refl) as (_ & VPM & _).
    cbn [firstn cells_size csize Nat.add length] in VPM. change (Z.of_nat 240) with 240 in VPM. rewrite TM in VPM.
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    hide STK. hide_slow. pose proof VEPimg as VEPimg'. unfold off_image in VEPimg'. cbn [al_image_lo al_image_hi LayoutP0] in VEPimg'. unfold IMG0_LO in TLO. unfold IMG0_HI in THI.
    call_fr (vep_match_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               bvmap_empty (Z_to_bv 32 0) m (pe_VEP E) Tb es (pslice E (x_p x) (pe_e E)) (pe_lo E)) by idtac.
    1:{ exact MI. }
    1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
    1:{ rewrite unsigned_lit by exact SPR. unfold VM_FRAME. rewrite PSP. clear - LOP. lia. }
    1:{ reflexivity. }
    1:{ exact (proj1 VPM). }
    1:{ clear - TLO. lia. }
    1:{ exact ITB. }
    1:{ exact WF. }
    1:{ exact STRS. }
    1:{ rewrite unsigned_lit by (clear - VERP Dlo Dhi CV PLT; unfold pe_e, pe_N in *; lia). apply pslice_bytes; [exact DBY| clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia]. }
    1:{ rewrite unsigned_lit by (clear - VERP Dlo Dhi CV PLT; unfold pe_e, pe_N in *; lia). rewrite pslice_length; [f_equal; clear; unfold pe_e, pe_N; lia| clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia]. }
    1:{ left. rewrite unsigned_lit by exact SPR. unfold VM_FRAME. rewrite PSP. clear - VEPhi CEIL LOP. lia. }
    1:{ left. rewrite unsigned_lit by exact SPR. unfold VM_FRAME. rewrite PSP. clear - THI CEIL LOP CV. lia. }
    1:{ left. rewrite (unsigned_lit (x_p x)) by (clear - VERP Dlo Dhi CV PLT; unfold pe_e, pe_N in *; lia). rewrite (unsigned_lit (pe_sp E)) by exact SPR.
        unfold VM_FRAME. rewrite PSP. rewrite pslice_length; [| clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia].
        clear - Dhi CEIL LOP PLE. unfold pe_e, pe_N in *. lia. }
    1:{ rewrite unsigned_lit by (clear - VERP Dlo Dhi CV PLT; unfold pe_e, pe_N in *; lia).
        rewrite pslice_length; [| clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia]. clear - Dhi CV PLE. unfold pe_e, pe_N in *. lia. }
    1:{ intros i e Hn Hp. left. rewrite unsigned_lit by exact SPR. unfold VM_FRAME. rewrite PSP. destruct (STRB i e Hn Hp) as [_ B]. revert B CEIL LOP CV. clear. unfold IMG0_LO. intros; lia. }
    clear STK. unhide_slow. rename POST into STK. rename MI0 into MI.
    (* [comment removed for export] *)
    clear ITB VPM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (ainv_stores E A m mc md _ _ PE0 AINV MU WM WZ) as AINVc;
      assert (STRS1 : mtab_strings mc es)
        by (destruct TAB4 as [(_ & X & _)|[(_ & X & _)|[(_ & X & _)|(_ & X & _)]]]; rewrite X;
            [apply tbl_bom_strings| apply tbl_attr_include_strings| apply tbl_esi_strings| apply tbl_starttag_strings]; exact MI)
    end.
    set (inp' := pslice E (x_p x) (pe_e E)) in *.
    assert (LINP : Z.of_nat (length inp') = pe_e E - x_p x) by (subst inp'; apply pslice_length; [clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia]).
    destruct (vm_find es inp') as [i|] eqn:VF; unfold vm_result; rewrite VF.
    - (* [comment removed for export] *)
      destruct (vm_find_some es inp' i WF VF) as (e & Hnth & CASES).
      destruct (TGT i e Hnth) as (k & S' & Hts & Esv & Hcell & Esval).
      pose proof (vm_find_lt es inp' i WF VF) as IL. rewrite mtab_cells_size in THI.
      assert (IR : 0 <= Tb + 16 * Z.of_nat i < 2^64) by (revert IL TLO THI; clear; intros; lia).
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 TLO. lia. } clear K1.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (ITB : ro_cells rsegs mc Tb (mtab_cells es))
          by (pose proof (img_stores E A m mc md _ _ PE0 AINV MU WZ IMG) as X; destruct X as (_ & _ & _ & _ & _ & _ & X1 & X2 & X3 & X4);
              destruct TAB4 as [(Y & X & _)|[(Y & X & _)|[(Y & X & _)|(Y & X & _)]]]; rewrite X, Y; assumption) end.
      pose proof (mtab_read_ptr rsegs _ Tb es i e _ ITB Hnth eq_refl) as RD1. unfold wa in RD1.
      zstep. clear RD1 ITB. cbv beta.
      (* [comment removed for export] *)
      assert (P804 : forall (p' : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc : mem),
        munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
        rw_cells rsegs mc (pe_VEP E) (vep_cells (fupd (x_v x) Fmatch_hit (Tb + 16 * Z.of_nat i)) (x_tag x) (x_q x)) ->
        rw_cells rsegs mc (pe_sp E) (pframe E j0 j8) ->
        bytes_at rsegs mc (pe_DATA E) (pe_inp E) -> stk rsegs mc (pe_lo E) (pe_sp E) ->
        ((me_ptr e = 0 /\ me_str e = [] /\ p' = x_p x) \/
         (me_ptr e <> 0 /\ is_prefixb (me_str e) inp' = true /\ p' = x_p x + Z.of_nat (length (me_str e)) /\ (1 <= length (me_str e) <= 8)%nat)) ->
        realizes rsegs (mkCfg (loop_ms E 0x1a950 p' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Tb + 16 * Z.of_nat i)) t3' t4' t5' t6' mc) md) T).
      { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc STKc HP. unfold loop_ms.
        clear VEPC FR DBY STK MI STRS1.
        unfold vep_cells in VEPCc. psimp_in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
        assert (LP : x_p x <= p' <= pe_e E).
        { destruct HP as [(_ & _ & ->)|(_ & PF & -> & _)]; [clear - PLE; unfold pe_e, pe_N; lia|].
          apply is_prefixb_length in PF. revert PF LINP PLE. clear. unfold pe_e, pe_N. intros. lia. }
        apply rz_go; [exact MDH| exact MDL|].
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          assert (ITB : ro_cells rsegs mc Tb (mtab_cells es))
            by (pose proof (img_stores E A m mc md _ _ PE0 AINV MUc WZ IMG) as X; destruct X as (_ & _ & _ & _ & _ & _ & X1 & X2 & X3 & X4);
                destruct TAB4 as [(Y & X & _)|[(Y & X & _)|[(Y & X & _)|(Y & X & _)]]]; rewrite X, Y; assumption) end.
        pose proof (mtab_read_svar rsegs _ Tb es i e _ ITB Hnth eq_refl) as RD2. unfold wa in RD2.
        zstep. clear RD2 ITB. cbv beta. rewrite Esv.
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          assert (IVV : ro_cells rsegs mc VEPVARS0 vepvars0)
            by (pose proof (img_stores E A m mc md _ _ PE0 AINV MUc WZ IMG) as X; destruct X as (_ & _ & _ & _ & _ & X1 & _); exact X1) end.
        pose proof (ro_cells_read_at rsegs _ VEPVARS0 vepvars0 k _ 8 _ IVV Hcell eq_refl eq_refl) as RD3. unfold wa in RD3. cbn [cbytes] in RD3.
        zstep. clear RD3 IVV. cbv beta.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
            by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MUc WMc WZ); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2 PSP; lia| exact HENV])
        end.
        (* [comment removed for export] *)
        assert (LKM : Tb = TBL_attr_include -> vct_xmlname (look E x) = true).
        { intros ETB. destruct (look_read rsegs E x _ DBYc ltac:(clear - VERP; lia) PLT) as (b & Hb & Hlk & _).
          pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR. rewrite <- Hlk.
          apply (proj1 (vct_namestart_facts _ BR ltac:(rewrite Hlk; apply (LOOKM eq_refl); [rewrite TM; exact ETB| exact PLT]))). }
        eapply (KL (PST p' S' (fupd (fupd (fupd (fupd (x_v x) Fmatch_hit (Tb + 16 * Z.of_nat i)) Fstate (st0 S')) Fmatch 0) Ftag_i 0)
                        (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
        2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MUc WMc WZ). }
        2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
        2:{ eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FRc]
                                 | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
        (* [comment removed for export] *)
        all: destruct TAB4 as [(ETb & Ees & Ets)|[(ETb & Ees & Ets)|[(ETb & Ees & Ets)|(ETb & Ees & Ets)]]]; subst ts es;
          (destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn in Hts; try discriminate Hts);
          injection Hts as EK ES'; subst k S'; cbn in Hnth; injection Hnth as Ee; subst e; cbn [me_ptr me_str length] in HP;
          rewrite ETb in TM, LKM, VEPCc |- *.
        (* [comment removed for export] *)
        17-32: psimp; intros _; split; [| discriminate]; unfold phi, rank; psimp; rewrite ST, TM;
          unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include; cbn [Z.eqb Pos.eqb];
          destruct HP as [(Z0 & _ & EP)|(NZ & PF & EP & LEN)]; subst p'; try (exfalso; clear - Z0; lia); try (exfalso; clear - NZ; lia);
          try (unfold look; cbn [x_p]; unfold look in LKM; rewrite (LKM eq_refl)); clear - PLT; lia.
        (* [comment removed for export] *)
        all: apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ.
        all: lazymatch goal with
          | |- _ <= _ Fver_p <= _ => clear - VERP LP; lia
          | |- _ <= pe_e _ => clear - LP; lia
          | |- 0 <= 0 <= 7 => clear; lia
          | |- _ = 0 \/ _ =>
              destruct ATTR as [A0|(A1 & A2 & A3)]; [left; exact A0| exfalso; destruct A3 as [A3|[A3|[A3|A3]]];
                [rewrite TM in A3; revert A3; clear; unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include; intros; lia
                | discriminate A3| discriminate A3| discriminate A3]]
          | |- _ + _ + _ + _ <= _ => revert OUT LP HP; unfold oacost, oicost; cbn [x_va x_vi x_st x_p x_vv]; clear; intros; lia
          | |- True -> _ <> 0 => intros _; apply ARMED; exact TM
          | |- True -> _ -> _ /\ _ => intros _ _; split; [exact (MATTR eq_refl TM)| cbn [Z.of_nat Pos.of_succ_nat]; first [left; clear; lia | right; clear; lia]]
          end. }
      (* [comment removed for export] *)
      pose proof (wf_ptr_nonneg _ _ _ WF Hnth) as PR.
      zstep. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        apply rz_stop. destruct CASES as [[Z0 ZS]|(NZ & _)]; [| exfalso; exact (NZ K2)].
        eapply (P804 (x_p x)); [exact MU| exact WM| exact MI| unfold vep_cells; psimp; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact STK
                              | left; split; [exact Z0| split; [exact ZS| reflexivity]]]. }
      destruct CASES as [[Z0 _]|(NZ & PF & LEN)]; [exfalso; exact (K2 Z0)|].
      pose proof (wf_entry _ _ _ WF Hnth NZ) as (_ & NONUL & _).
      (* [comment removed for export] *)
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (STRS2 : mtab_strings mc es)
          by (destruct TAB4 as [(_ & X & _)|[(_ & X & _)|[(_ & X & _)|(_ & X & _)]]]; rewrite X;
              [apply tbl_bom_strings| apply tbl_attr_include_strings| apply tbl_esi_strings| apply tbl_starttag_strings]; assumption) end.
      destruct (STRS2 i e Hnth NZ) as (slack & SB & SPAD & SLEN). clear STRS2.
      hide_slow.
      call_fr (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) _ (me_str e) slack) by idtac.
      1:{ rewrite unsigned_lit by exact PR. exact SB. }
      1:{ exact NONUL. }
      1:{ rewrite unsigned_lit by exact PR. exact SPAD. }
      1:{ assumption. }
      unhide_slow. rename POST into SB2.
      try match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      (* [comment removed for export] *)
      assert (PR2 : 0 <= x_p x + Z.of_nat (length (me_str e)) < 2^64) by (revert LEN VERP Dlo PLT Dhi CV; clear; unfold pe_e, pe_N; intros; lia).
      zstep.
      apply rz_stop.
      eapply (P804 (x_p x + Z.of_nat (length (me_str e))));
        [exact MU| exact WM| assumption| unfold vep_cells; psimp; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact STK
        | right; split; [exact NZ| split; [exact PF| split; [reflexivity| exact LEN]]]].
    - (* [comment removed for export] *)
      pose proof (vm_find_none es inp' WF VF) as LIN.
      assert (NR : 0 <= pe_e E - x_p x <= 7) by (revert LIN LINP PLT; clear; intros; lia).
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. } clear K1.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3.
      { exfalso. revert K3 NR VERP Dlo PLT Dhi CV. clear. unfold pe_e, pe_N. intros. first [rewrite Z.mod_small in K3 by lia | idtac]. lia. }
      clear K3.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      set (n := Z.to_nat (pe_e E - x_p x)).
      assert (LN : length inp' = n) by (subst n; revert LINP; clear; intros; lia).
      assert (LT8 : (n <= 8)%nat) by (subst n; revert NR; clear; intros; lia).
      pose proof (pd_split3 rsegs _ (pe_VEP E) _ 41 (CB 8 (x_tag x)) VEPC eq_refl) as (VXA & VXT & VXB).
      cbn [firstn skipn cells_size csize Nat.add length] in VXA, VXT, VXB.
      change (Z.of_nat 256) with 256 in VXT. change (Z.of_nat 256) with 256 in VXB. change (Z.of_nat 8) with 8 in VXB.
      replace (pe_VEP E + 256 + 8) with (pe_VEP E + 264) in VXB by (clear; lia).
      apply (rw_cells_recast rsegs _ (pe_VEP E + 256) _ [CB n (firstn n (x_tag x)); CB (8 - n) (skipn n (x_tag x))]) in VXT;
        [| cbn; rewrite firstn_length, skipn_length; revert TAG LT8; clear; intros; repeat split; lia
         | cbn [cells_bytes cbytes]; rewrite !app_nil_r; rewrite firstn_skipn; reflexivity].
      apply (proj1 (rw_cells_app rsegs _ _ [CB n (firstn n (x_tag x))] [CB (8 - n) (skipn n (x_tag x))])) in VXT.
      destruct VXT as [VXT1 VXT2]. cbn [cells_size csize Nat.add] in VXT2.
      clear VEPC. hide_slow.
      call_fr (memcpy_spec_z _ _ _ _ _ _ _ _ _ (pe_VEP E + 256) (x_p x) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 bvmap_empty (Z_to_bv 32 0) _ inp' (firstn n (x_tag x))) by idtac.
      1:{ rewrite LINP. unfold pe_e, pe_N. reflexivity. }
      1:{ subst inp'. apply pslice_bytes; [exact DBY| clear - VERP; lia| exact PLE| clear; unfold pe_e, pe_N; lia]. }
      1:{ rewrite LN. exact VXT1. }
      1:{ revert DJ_VD VERP PLE NR. clear. unfold pe_e, pe_N. intros. lia. }
      1:{ clear - VEPhi CV. lia. }
      1:{ clear - PLT Dhi CV. unfold pe_e, pe_N in *. lia. }
      1:{ exact MI. }
      unhide_slow.
      lazymatch goal with H : rw_cells rsegs ?mc (pe_VEP E + 256) [CB (length inp') inp'] |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into DST end.
      try match goal with |- context [ret_pc (Z_to_bv 64 ?n0)] =>
        replace (ret_pc (Z_to_bv 64 n0)) with (Z_to_bv 64 n0) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      (* [comment removed for export] *)
      set (tag' := inp' ++ skipn n (x_tag x)).
      assert (TAG' : length tag' = 8%nat) by (subst tag'; rewrite length_app, skipn_length, LN; revert TAG LT8; clear; intros; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (VEPC : rw_cells rsegs mf (pe_VEP E) (vep_cells (fupd (x_v x) Fmatch_hit 0) tag' (x_q x))) end.
      { subst tag'. unfold vep_cells. psimp. rewrite STATE.
        lazymatch type of VXA with rw_cells _ _ _ ?pre =>
          apply (pd_join3 rsegs _ (pe_VEP E) pre (CB 8 (inp' ++ skipn n (x_tag x)))); [exact VXA| |] end.
        - cbn [cells_size csize Nat.add length]. change (Z.of_nat 256) with 256.
          apply (rw_cells_recast rsegs _ (pe_VEP E + 256) [CB n inp'; CB (8 - n) (skipn n (x_tag x))]).
          + apply (proj2 (rw_cells_app rsegs _ _ [CB n inp'] [CB (8 - n) (skipn n (x_tag x))])).
            split; [rewrite <- LN; exact DST|]. cbn [cells_size csize Nat.add]. exact VXT2.
          + cbn. rewrite length_app, skipn_length, LN. revert TAG LT8. clear. intros. repeat split; lia.
          + cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
        - cbn [cells_size csize Nat.add length]. change (Z.of_nat 256) with 256. change (Z.of_nat 8) with 8.
          replace (pe_VEP E + 256 + 8) with (pe_VEP E + 264) by (clear; lia). exact VXB. }
      clear VXA VXB VXT2 DST POST. unfold vep_cells in VEPC. psimp_in VEPC. rewrite STATE in VEPC.
      (* [comment removed for export] *)
      assert (NR64 : 0 <= pe_e E - x_p x < 2^64) by (revert NR; clear; intros; lia).
      assert (NR32 : 0 <= pe_e E - x_p x < 2^32) by (revert NR; clear; intros; lia).
      zstep. zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      set (v' := fupd (fupd (fupd (x_v x) Fmatch_hit 0) Ftag_i (pe_e E - x_p x)) Fstate (st0 S_MatchBuf)).
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MU WM WZ); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2 PSP; lia| exact HENV])
      end.
      eapply (KX (PST (pe_e E) S_MatchBuf v' tag' (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; subst v'; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; subst v'; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      2:{ reflexivity. }
      subst v'. apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
      + (* [comment removed for export] *) clear - VERP PLE. unfold pe_e, pe_N. lia.
      + (* [comment removed for export] *) revert OUT PLE. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. unfold pe_e, pe_N. intros; lia.
  Qed.
End S.
