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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c V_Paq9r V_PKit V_VSle5 Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma pd_split3 : forall segs m A cs k c,
  rw_cells segs m A cs -> nth_error cs k = Some c ->
  rw_cells segs m A (firstn k cs) /\
  rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs))) [c] /\
  rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs)) + Z.of_nat (csize c)) (skipn (S k) cs).
Proof.
  intros segs m A cs k c RC Hk.
  assert (E : cs = firstn k cs ++ [c] ++ skipn (S k) cs).
  { rewrite <- (firstn_skipn k cs) at 1. f_equal.
    revert Hk. clear. revert cs. induction k as [|k IH]; intros [|x cs] Hk; cbn in *; try discriminate.
    - inversion Hk. reflexivity.
    - apply IH. exact Hk. }
  rewrite E in RC. apply rw_cells_app in RC. destruct RC as [R1 R23]. apply rw_cells_app in R23. destruct R23 as [R2 R3].
  split; [exact R1|]. split; [exact R2|]. cbn [cells_size Nat.add] in R3. rewrite Nat.add_0_r in R3.
  eapply rwc_eq; [exact R3| lia].
Qed.

Lemma pd_join3 : forall segs m A pre c post,
  rw_cells segs m A pre ->
  rw_cells segs m (A + Z.of_nat (cells_size pre)) [c] ->
  rw_cells segs m (A + Z.of_nat (cells_size pre) + Z.of_nat (csize c)) post ->
  rw_cells segs m A (pre ++ [c] ++ post).
Proof.
  intros segs m A pre c post R1 R2 R3. apply rw_cells_app. split; [exact R1|]. apply rw_cells_app. split; [exact R2|].
  cbn [cells_size Nat.add]. rewrite Nat.add_0_r. eapply rwc_eq; [exact R3| lia].
Qed.

Lemma pd_cells_attr_vsb : forall v tag q,
  firstn 36 (vep_cells v tag q) ++ [C8 (Z_to_bv 64 0)] ++ skipn 37 (vep_cells v tag q) = vep_cells (fupd v Fattr_vsb 0) tag q.
Proof. intros. reflexivity. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Definition after_destroy_attr (x : pst) : pst :=
    PST (x_p x) (x_st x) (fupd (x_v x) Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma destroy_attr_gen : forall (E : penv) (x : pst) (A : AS) (m0 m : mem) (md : Model) (T : TSet) (ret : Z)
      (W : list ivl) (v' : vep) (fj0 fj8 : word)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (ps : Z),
    penv_ok E -> pinv E x A m0 -> ainv A m0 md ->
    munch W m0 m -> wmono rsegs m0 m ->
    wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x] W ->
    (forall a, h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320 -> outside W a) ->
    mem_inv rsegs m -> stk rsegs m (pe_lo E) (pe_sp E) -> rw_cells rsegs m (pe_sp E) (pframe E fj0 fj8) ->
    rw_cells rsegs m (pe_VEP E) (vep_cells v' (x_tag x) (x_q x)) ->
    v' Fattr_vsb = x_v x Fattr_vsb -> v' Finclude_src = x_v x Finclude_src ->
    x_va x <> None -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A1 : AS) (m1 : mem) (md1 : Model),
        ainv A1 m1 md1 -> mem_inv rsegs m1 -> md_frame md md1 ->
        stk rsegs m1 (pe_lo E) (pe_sp E) -> rw_cells rsegs m1 (pe_sp E) (pframe E fj0 fj8) ->
        rw_cells rsegs m1 (pe_VEP E) (vep_cells (fupd v' Fattr_vsb 0) (x_tag x) (x_q x)) ->
        img_ok0 m1 -> henv_ok LayoutP0 VI0 (pe_H E) m1 -> data_obj LayoutP0 A1 m1 (pe_DATA E) (pe_inp E) ->
        vsb_obj LayoutP0 A1 m1 (pe_S E) (x_vv x) false ->
        a_live A1 (pe_wa E) = Some 40 -> a_live A1 (pe_VEP E) = Some 312 ->
        vi_world E (PST (x_p x) (x_st x) (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A1 m1 ->
        (* [comment removed for export] *)
        a_livebytes A1 = pe_LB0 E - 56 + pw_bytes (x_vv x) None (x_vi x) -> a_nlive A1 = pe_NL0 E + pw_nlive None (x_vi x) ->
        (forall p st, hstep E (PST p st v' (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x))
                              (PST p st (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A A1 m m1) ->
        realizes rsegs (mkCfg (loop_ms E ret ps (Z_to_bv 64 ret) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7 t3' t4' t5' t6' m1) md1) T) ->
    realizes rsegs (mkCfg (loop_ms E VSB_destroy_entry ps (Z_to_bv 64 ret) t0 t1 t2
                             (Z_to_bv 64 (pe_VEP E + 224)) a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m) md) T.
  Proof.
    intros until ps. intros PE PI AINV0 MU WM WZ NCNT MI' STK' FR' VEPC' EAV EIS VNN RR RET K.
    world_open PE PI AINV0.
    clear VEPC FR STK MI.
    pose proof (ainv_stores E A m0 m md _ _ PE0 AINV0 MU WM WZ) as AINV.
    assert (HENV' : henv_ok LayoutP0 VI0 (pe_H E) m) by (eapply (henv_stores E A m0 m md _ _ PE0 AINV0 MU WM WZ); [exact NCNT| exact HENV]); clear HENV.
    assert (IMG' : img_ok0 m) by (eapply (img_stores E A m0 m md _ _ PE0 AINV0 MU WZ); exact IMG); clear IMG.
    assert (VSBO' : vsb_obj LayoutP0 A m (pe_S E) (x_vv x) false) by (eapply (vsb_obj_stores E A m0 m md _ _ PE0 AINV0 MU WM WZ); [in_list| in_list| exact VSBO]); clear VSBO.
    assert (DATA' : data_obj LayoutP0 A m (pe_DATA E) (pe_inp E)) by (eapply (data_obj_stores E A m0 m md _ _ PE0 AINV0 MU WZ); [in_list| exact DATA]); clear DATA DBY.
    assert (VI' : vi_world E x A m) by (unfold vi_world; world_stores VI PE0 AINV0 MU WM WZ).
    destruct (x_va x) as [y|] eqn:EVA; [| exfalso; exact (VNN eq_refl)].
    (first [ dand4 VA as ANZ AOBJ0 AROOM AAP | destruct VA as (ANZ & AOBJ0 & AROOM & AAP) ]).
    assert (AOBJ : vsb_obj LayoutP0 A m (x_v x Fattr_vsb) y false) by (eapply (vsb_obj_stores E A m0 m md _ _ PE0 AINV0 MU WM WZ); [in_list| in_list| exact AOBJ0]); clear AOBJ0.
    clear MU WM WZ VI. unfold vi_world in VI'.
    (first [ pose proof (AOBJ) as dR_7; dand6 dR_7 as _ _ LAS LAB ASB _ | pose proof AOBJ as (_ & _ & LAS & LAB & ASB & _) ]).
    unfold oabuf in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI. rewrite EVA in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI.
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LAS LVEP D_AV) as DXA.
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LAB LVEP D_ABV) as DXB.
    (* [comment removed for export] *)
    pose proof (rw_cells_bound _ _ _ _ VEPC') as VEPB'.
    unfold vep_cells in VEPC'. rewrite EAV in VEPC'.
    (first [ pose proof ((pd_split3 rsegs m (pe_VEP E) _ 36 (C8 (Z_to_bv 64 (x_v x Fattr_vsb))) VEPC' eq_refl)) as dR_8; dand3 dR_8 as VA VP VB | pose proof (pd_split3 rsegs m (pe_VEP E) _ 36 (C8 (Z_to_bv 64 (x_v x Fattr_vsb))) VEPC' eq_refl) as (VA & VP & VB) ]).
    cbn [firstn skipn cells_size csize Nat.add length] in VA, VP, VB.
    change (Z.of_nat 224) with 224 in VP. change (Z.of_nat 224) with 224 in VB. change (Z.of_nat 8) with 8 in VB.
    replace (pe_VEP E + 224 + 8) with (pe_VEP E + 232) in VB by (clear; lia).
    assert (SPR : 0 <= pe_sp E < 2^64) by (clear - FRB; lia).
    unfold loop_ms.
    eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A (pe_VEP E + 224) (x_v x Fattr_vsb) y false (pe_lo E));
      [ exact AINV | exact MI' | reflexivity | exact VP
      | right; exists (pe_VEP E), 312; split; [exact LVEP|]; split; [cbn; intros [X|[X|X]]; [exact (D_AV X)| exact (D_ABV X)| exact X] | clear; lia]
      | exact AOBJ | reflexivity
      | rewrite unsigned_lit by exact SPR; rewrite PSP, Zminus_mod, G1; reflexivity
      | rewrite unsigned_lit by exact RR; exact RET
      | rewrite unsigned_lit by exact SPR; exact STK' | exact CEIL
      | rewrite unsigned_lit by exact SPR; revert LOP PSP; clear; unfold DESTROY_STACK, FREE_STACK; intros; lia
      | rewrite unsigned_lit by exact SPR; revert G3 PSP; clear; unfold HFRAME; intros; lia | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 AINV1 MI1 MDF ST1 PSC DEADS DEADB LIVEq LBd NLd CF.
    rewrite unsigned_lit in ST1, CF by exact SPR.
    rewrite (ret_pc_even ret RR RET).
    set (Vd := fun a : Z => blk (x_v x Fattr_vsb) 40 a \/ blk (vb_buf y) (vb_size y) a \/ pe_VEP E + 224 <= a < pe_VEP E + 224 + 8) in CF.
    assert (HC : hcover A [pe_S E; vb_buf (x_vv x); pe_DATA E] Vd).
    { intros a [X|[X|X]].
      - eapply hcover_blk; [exact LAS| wz_not_in| exact X].
      - eapply hcover_blk; [exact LAB| wz_not_in| exact X].
      - eapply hcover_rng; [exact LVEP| wz_not_in| clear - X; lia]. }
    pose proof (hcover_vcover (pe_H E) _ _ _ HC) as CV1.
    assert (WIN : alloc_ceiling <= pe_sp E - DESTROY_STACK) by (revert CEIL LOP PSP; clear; unfold DESTROY_STACK, FREE_STACK; intros; lia).
    assert (WPOS : 0 <= DESTROY_STACK) by (clear; unfold DESTROY_STACK, FREE_STACK; lia).
    assert (SPH : pe_sp E <= h_sp (pe_H E)) by (rewrite PSP; clear; lia).
    assert (LK : forall p k, a_live A p = Some k -> p <> x_v x Fattr_vsb -> p <> vb_buf y -> a_live A1 p = Some k)
      by (intros p k Hp N1 N2; rewrite (LIVEq p N1 N2); exact Hp).
    assert (LVEP1 : a_live A1 (pe_VEP E) = Some 312) by (apply LK; [exact LVEP| exact (not_eq_sym D_AV)| exact (not_eq_sym D_ABV)]).
    assert (LVS1 : a_live A1 (pe_S E) = Some 40) by (apply LK; [exact LVS| exact (not_eq_sym D_AS)| exact (not_eq_sym D_ABS)]).
    assert (LVB1 : a_live A1 (vb_buf (x_vv x)) = Some (vb_size (x_vv x))) by (apply LK; [exact LVB| exact (not_eq_sym D_AB)| exact (not_eq_sym D_ABB)]).
    assert (LDATA1 : a_live A1 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))) by (apply LK; [exact LDATA| exact (not_eq_sym D_AD)| exact (not_eq_sym D_ABD)]).
    assert (WAL1 : a_live A1 (pe_wa E) = Some 40) by (apply LK; [exact WAL| exact (not_eq_sym D_AW)| exact (not_eq_sym D_ABW)]).
    assert (FR1 : rw_cells rsegs m1 (pe_sp E) (pframe E fj0 fj8)).
    { eapply (pframe_call E A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [pe_S E; vb_buf (x_vv x); pe_DATA E]);
        [exact PE| exact AINV| exact CF| exact WIN| exact WPOS| clear; lia| exact CV1| exact FR']. }
    assert (IMG1 : img_ok0 m1).
    { eapply (img_call (pe_H E) A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF HG WIN); [exact CV1| exact IMG']. }
    assert (HENV1 : henv_ok LayoutP0 VI0 (pe_H E) m1).
    { eapply (henv_call (pe_H E) A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF HG WIN SPH); [exact HC| exact HENV']. }
    assert (DATA1 : data_obj LayoutP0 A1 m1 (pe_DATA E) (pe_inp E)).
    { eapply (data_obj_call (pe_H E) A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF HG WIN);
        [exact CV1| in_list| exact LDATA1| exact DATA']. }
    assert (VSBO1 : vsb_obj LayoutP0 A1 m1 (pe_S E) (x_vv x) false).
    { eapply (vsb_obj_call (pe_H E) A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF HG WIN);
        [exact CV1| in_list| in_list| exact LVS1| exact LVB1| exact VSBO']. }
    assert (VI1 : vi_world E (PST (x_p x) (x_st x) (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A1 m1).
    { unfold vi_world. cbn [x_vi x_v x_va x_vv fupd vf_beq vf_index N.eqb Pos.eqb]. rewrite EIS.
      destruct (x_vi x) as [yi|] eqn:EVI; [| exact VI'].
      (first [ dand6 VI' as Q1 Q2 Q3 Q3b Q4 Q5 | destruct VI' as (Q1 & Q2 & Q3 & Q3b & Q4 & Q5) ]). (first [ pose proof ((D_AI ltac:(discriminate) ltac:(discriminate))) as dR_10; dand4 dR_10 as NIA NIB NBA NBB | destruct (D_AI ltac:(discriminate) ltac:(discriminate)) as (NIA & NIB & NBA & NBB) ]).
      unfold oibuf in NBA, NBB, D_IBV. rewrite EVI in NBA, NBB, D_IBV.
      refine (conj Q1 (conj _ (conj Q3 (conj Q3b (conj Q4 I))))).
      assert (HCi : hcover A [x_v x Finclude_src; vb_buf yi] Vd).
      { intros a [X|[X|X]].
        - eapply hcover_blk; [exact LAS| wz_not_in| exact X].
        - eapply hcover_blk; [exact LAB| wz_not_in| exact X].
        - eapply hcover_rng; [exact LVEP| wz_not_in| clear - X; lia]. }
      eapply (vsb_obj_call (pe_H E) A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [x_v x Finclude_src; vb_buf yi] AINV CF HG WIN);
        [exact (hcover_vcover (pe_H E) _ _ _ HCi)| in_list| in_list
        | apply LK; [exact (proj1 (proj2 (proj2 Q2)))| exact NIA| exact NIB]
        | apply LK; [exact (proj1 (proj2 (proj2 (proj2 Q2))))| exact NBA| exact NBB]
        | exact Q2]. }
    assert (AVA : avoids_call (pe_sp E) DESTROY_STACK Vd (pe_VEP E) 224).
    { split; [left; revert VEPhi WIN; clear; intros; lia|].
      intros i Hi X. subst Vd. cbn beta in X. unfold blk in X. revert Hi X DXA DXB. clear. intros; lia. }
    assert (AVB : avoids_call (pe_sp E) DESTROY_STACK Vd (pe_VEP E + 232) 80).
    { split; [left; revert VEPhi WIN; clear; intros; lia|].
      intros i Hi X. subst Vd. cbn beta in X. unfold blk in X. revert Hi X DXA DXB. clear. intros; lia. }
    apply (rw_cells_ccall LayoutP0 A A1 (pe_sp E) DESTROY_STACK Vd nowhere m m1 CF (pe_VEP E)) in VA;
      [| eapply crange_block; [exact AINV| exact LVEP| clear; lia| clear; cbn; lia| clear; cbn; lia] | cbn [cells_size csize Nat.add length]; exact AVA].
    apply (rw_cells_ccall LayoutP0 A A1 (pe_sp E) DESTROY_STACK Vd nowhere m m1 CF (pe_VEP E + 232)) in VB;
      [| eapply crange_block; [exact AINV| exact LVEP| clear; lia| clear; cbn; lia| clear; cbn; lia]
       | cbn [cells_size csize Nat.add length]; exact AVB].
    assert (VEPC1 : rw_cells rsegs m1 (pe_VEP E) (vep_cells (fupd v' Fattr_vsb 0) (x_tag x) (x_q x))).
    { rewrite <- pd_cells_attr_vsb. unfold vep_cells. cbn [firstn skipn].
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (pd_join3 rsegs m1 (pe_VEP E) pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VB| cbn [cells_size csize Nat.add length]; clear; lia]. }
    clear VA VB PSC AVA AVB.
    assert (HS : forall p st, hstep E (PST p st v' (x_tag x) (x_q x) (x_vv x) (Some y) (x_vi x))
                                (PST p st (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A A1 m m1).
    { intros p st.
      eapply (hstep_call0 E _ _ A A1 m m1 DESTROY_STACK Vd);
        [ exact CF
        | clear; unfold DESTROY_STACK; unfold_stacks_g; lia
        | eapply parse_window_mapped; [exact PE| exact ST1| exact FR1]
        | intros a [X|[X|X]]; unfold pzone; cbn [x_v x_va x_vi x_vv]; rewrite ?EAV;
          [ right; right; right; left; left; exact X
          | right; right; right; left; right; exact X
          | left; unfold blk; split; [clear - VEPlo; lia| clear - X; lia] ]
        | intros p0 k Hp NB; apply LK; [exact Hp| |]; intros ->; apply NB; unfold pst_blocks; cbn [x_v x_va x_vi x_vv]; rewrite ?EAV; right; left; [left|right]; reflexivity
        | unfold pst_blocks; psimp; rewrite ?EIS; intros p0 [Hp|[Hp|Hp]]; [left; left; exact Hp| destruct Hp| left; right; right; exact Hp]
        | unfold parse_new, pzone; psimp; rewrite ?EAV, ?EIS; cbn [option_map]; intros a [Ha|[Ha|Ha]];
          [ right; right; left; exact Ha | destruct Ha | right; right; right; right; left; destruct (x_vi x); [exact Ha| destruct Ha] ] ]. }
    unfold loop_ms in K.
    assert (LB1 : a_livebytes A1 = pe_LB0 E - 56 + pw_bytes (x_vv x) None (x_vi x)) by (rewrite LBd, LB; rewrite ?EVA; unfold pw_bytes; clear; lia).
    assert (NL1 : a_nlive A1 = pe_NL0 E + pw_nlive None (x_vi x)) by (rewrite NLd, NL; rewrite ?EVA; unfold pw_nlive; clear; lia).
    exact (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 m1 md1 AINV1 MI1 MDF ST1 FR1 VEPC1 IMG1 HENV1 DATA1 VSBO1 WAL1 LVEP1 VI1 LB1 NL1 HS).
  Qed.
  (* [comment removed for export] *)
  Lemma destroy_attr_fin : forall (E : penv) (x : pst) (A : AS) (m0 m : mem) (md : Model) (T : TSet) (ret : Z)
      (W : list ivl) (v' : vep) (y yf : vsb_rec) (fin : bool) (fj0 fj8 : word)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (ps : Z),
    penv_ok E -> pinv E x A m0 -> ainv A m0 md ->
    munch W m0 m -> wmono rsegs m0 m ->
    wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Finclude_src; oibuf x] W ->
    mem_inv rsegs m -> stk rsegs m (pe_lo E) (pe_sp E) -> rw_cells rsegs m (pe_sp E) (pframe E fj0 fj8) ->
    henv_ok LayoutP0 VI0 (pe_H E) m ->
    rw_cells rsegs m (pe_VEP E) (vep_cells v' (x_tag x) (x_q x)) ->
    v' Fattr_vsb = x_v x Fattr_vsb -> v' Finclude_src = x_v x Finclude_src ->
    x_va x = Some y -> vsb_obj LayoutP0 A m (x_v x Fattr_vsb) yf fin -> vb_buf yf = vb_buf y -> vb_size yf = vb_size y ->
    0 <= ret < 2^64 -> ret mod 2 = 0 ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A1 : AS) (m1 : mem) (md1 : Model),
        ainv A1 m1 md1 -> mem_inv rsegs m1 -> md_frame md md1 ->
        stk rsegs m1 (pe_lo E) (pe_sp E) -> rw_cells rsegs m1 (pe_sp E) (pframe E fj0 fj8) ->
        rw_cells rsegs m1 (pe_VEP E) (vep_cells (fupd v' Fattr_vsb 0) (x_tag x) (x_q x)) ->
        img_ok0 m1 -> henv_ok LayoutP0 VI0 (pe_H E) m1 -> data_obj LayoutP0 A1 m1 (pe_DATA E) (pe_inp E) ->
        vsb_obj LayoutP0 A1 m1 (pe_S E) (x_vv x) false ->
        a_live A1 (pe_wa E) = Some 40 -> a_live A1 (pe_VEP E) = Some 312 ->
        vi_world E (PST (x_p x) (x_st x) (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A1 m1 ->
        (* [comment removed for export] *)
        a_livebytes A1 = pe_LB0 E - 56 + pw_bytes (x_vv x) None (x_vi x) -> a_nlive A1 = pe_NL0 E + pw_nlive None (x_vi x) ->
        (forall p st, hstep E (PST p st v' (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x))
                              (PST p st (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A A1 m m1) ->
        realizes rsegs (mkCfg (loop_ms E ret ps (Z_to_bv 64 ret) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7 t3' t4' t5' t6' m1) md1) T) ->
    realizes rsegs (mkCfg (loop_ms E VSB_destroy_entry ps (Z_to_bv 64 ret) t0 t1 t2
                             (Z_to_bv 64 (pe_VEP E + 224)) a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m) md) T.
  Proof.
    intros until ps. intros PE PI AINV0 MU WM WZ MI' STK' FR' HENV' VEPC' EAV EIS EVA AOBJ EYB EYS RR RET K.
    world_open PE PI AINV0.
    clear VEPC FR STK MI HENV.
    pose proof (ainv_stores E A m0 m md _ _ PE0 AINV0 MU WM WZ) as AINV.
    assert (IMG' : img_ok0 m) by (eapply (img_stores E A m0 m md _ _ PE0 AINV0 MU WZ); exact IMG); clear IMG.
    assert (VSBO' : vsb_obj LayoutP0 A m (pe_S E) (x_vv x) false) by (eapply (vsb_obj_stores E A m0 m md _ _ PE0 AINV0 MU WM WZ); [in_list| in_list| exact VSBO]); clear VSBO.
    assert (DATA' : data_obj LayoutP0 A m (pe_DATA E) (pe_inp E)) by (eapply (data_obj_stores E A m0 m md _ _ PE0 AINV0 MU WZ); [in_list| exact DATA]); clear DATA DBY.
    assert (VI' : vi_world E x A m) by (unfold vi_world; world_stores VI PE0 AINV0 MU WM WZ).
    rewrite EVA in VA. (first [ dand4 VA as ANZ AOBJ0 AROOM AAP | destruct VA as (ANZ & AOBJ0 & AROOM & AAP) ]).
    (first [ pose proof (AOBJ0) as dR_12; dand6 dR_12 as _ _ LAS LAB0 ASB _ | pose proof AOBJ0 as (_ & _ & LAS & LAB0 & ASB & _) ]). clear AOBJ0.
    (first [ pose proof (AOBJ) as dR_13; dand6 dR_13 as _ _ _ LAB _ _ | pose proof AOBJ as (_ & _ & _ & LAB & _ & _) ]). rewrite EYB, EYS in LAB.
    clear MU WM WZ VI. unfold vi_world in VI'.
    unfold oabuf in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI. rewrite EVA in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI.
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LAS LVEP D_AV) as DXA.
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LAB LVEP D_ABV) as DXB.
    (* [comment removed for export] *)
    pose proof (rw_cells_bound _ _ _ _ VEPC') as VEPB'.
    unfold vep_cells in VEPC'. rewrite EAV in VEPC'.
    (first [ pose proof ((pd_split3 rsegs m (pe_VEP E) _ 36 (C8 (Z_to_bv 64 (x_v x Fattr_vsb))) VEPC' eq_refl)) as dR_14; dand3 dR_14 as VA VP VB | pose proof (pd_split3 rsegs m (pe_VEP E) _ 36 (C8 (Z_to_bv 64 (x_v x Fattr_vsb))) VEPC' eq_refl) as (VA & VP & VB) ]).
    cbn [firstn skipn cells_size csize Nat.add length] in VA, VP, VB.
    change (Z.of_nat 224) with 224 in VP. change (Z.of_nat 224) with 224 in VB. change (Z.of_nat 8) with 8 in VB.
    replace (pe_VEP E + 224 + 8) with (pe_VEP E + 232) in VB by (clear; lia).
    assert (SPR : 0 <= pe_sp E < 2^64) by (clear - FRB; lia).
    unfold loop_ms.
    eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A (pe_VEP E + 224) (x_v x Fattr_vsb) yf fin (pe_lo E));
      [ exact AINV | exact MI' | reflexivity | exact VP
      | right; exists (pe_VEP E), 312; split; [exact LVEP|]; split; [cbn; rewrite EYB; intros [X|[X|X]]; [exact (D_AV X)| exact (D_ABV X)| exact X] | clear; lia]
      | exact AOBJ | reflexivity
      | rewrite unsigned_lit by exact SPR; rewrite PSP, Zminus_mod, G1; reflexivity
      | rewrite unsigned_lit by exact RR; exact RET
      | rewrite unsigned_lit by exact SPR; exact STK' | exact CEIL
      | rewrite unsigned_lit by exact SPR; revert LOP PSP; clear; unfold DESTROY_STACK, FREE_STACK; intros; lia
      | rewrite unsigned_lit by exact SPR; revert G3 PSP; clear; unfold HFRAME; intros; lia | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 AINV1 MI1 MDF ST1 PSC DEADS DEADB LIVEq LBd NLd CF.
    rewrite unsigned_lit in ST1, CF by exact SPR. rewrite ?EYB, ?EYS in CF. rewrite ?EYB in DEADB. rewrite ?EYB in LIVEq.
    rewrite (ret_pc_even ret RR RET).
    set (Vd := fun a : Z => blk (x_v x Fattr_vsb) 40 a \/ blk (vb_buf y) (vb_size y) a \/ pe_VEP E + 224 <= a < pe_VEP E + 224 + 8) in CF.
    assert (HC : hcover A [pe_S E; vb_buf (x_vv x); pe_DATA E] Vd).
    { intros a [X|[X|X]].
      - eapply hcover_blk; [exact LAS| wz_not_in| exact X].
      - eapply hcover_blk; [exact LAB| wz_not_in| exact X].
      - eapply hcover_rng; [exact LVEP| wz_not_in| clear - X; lia]. }
    pose proof (hcover_vcover (pe_H E) _ _ _ HC) as CV1.
    assert (WIN : alloc_ceiling <= pe_sp E - DESTROY_STACK) by (revert CEIL LOP PSP; clear; unfold DESTROY_STACK, FREE_STACK; intros; lia).
    assert (WPOS : 0 <= DESTROY_STACK) by (clear; unfold DESTROY_STACK, FREE_STACK; lia).
    assert (SPH : pe_sp E <= h_sp (pe_H E)) by (rewrite PSP; clear; lia).
    assert (LK : forall p k, a_live A p = Some k -> p <> x_v x Fattr_vsb -> p <> vb_buf y -> a_live A1 p = Some k)
      by (intros p k Hp N1 N2; rewrite (LIVEq p N1 N2); exact Hp).
    assert (LVEP1 : a_live A1 (pe_VEP E) = Some 312) by (apply LK; [exact LVEP| exact (not_eq_sym D_AV)| exact (not_eq_sym D_ABV)]).
    assert (LVS1 : a_live A1 (pe_S E) = Some 40) by (apply LK; [exact LVS| exact (not_eq_sym D_AS)| exact (not_eq_sym D_ABS)]).
    assert (LVB1 : a_live A1 (vb_buf (x_vv x)) = Some (vb_size (x_vv x))) by (apply LK; [exact LVB| exact (not_eq_sym D_AB)| exact (not_eq_sym D_ABB)]).
    assert (LDATA1 : a_live A1 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))) by (apply LK; [exact LDATA| exact (not_eq_sym D_AD)| exact (not_eq_sym D_ABD)]).
    assert (WAL1 : a_live A1 (pe_wa E) = Some 40) by (apply LK; [exact WAL| exact (not_eq_sym D_AW)| exact (not_eq_sym D_ABW)]).
    assert (FR1 : rw_cells rsegs m1 (pe_sp E) (pframe E fj0 fj8)).
    { eapply (pframe_call E A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [pe_S E; vb_buf (x_vv x); pe_DATA E]);
        [exact PE| exact AINV| exact CF| exact WIN| exact WPOS| clear; lia| exact CV1| exact FR']. }
    assert (IMG1 : img_ok0 m1).
    { eapply (img_call (pe_H E) A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF HG WIN); [exact CV1| exact IMG']. }
    assert (HENV1 : henv_ok LayoutP0 VI0 (pe_H E) m1).
    { eapply (henv_call (pe_H E) A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF HG WIN SPH); [exact HC| exact HENV']. }
    assert (DATA1 : data_obj LayoutP0 A1 m1 (pe_DATA E) (pe_inp E)).
    { eapply (data_obj_call (pe_H E) A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF HG WIN);
        [exact CV1| in_list| exact LDATA1| exact DATA']. }
    assert (VSBO1 : vsb_obj LayoutP0 A1 m1 (pe_S E) (x_vv x) false).
    { eapply (vsb_obj_call (pe_H E) A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF HG WIN);
        [exact CV1| in_list| in_list| exact LVS1| exact LVB1| exact VSBO']. }
    assert (VI1 : vi_world E (PST (x_p x) (x_st x) (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A1 m1).
    { unfold vi_world. cbn [x_vi x_v x_va x_vv fupd vf_beq vf_index N.eqb Pos.eqb]. rewrite EIS.
      destruct (x_vi x) as [yi|] eqn:EVI; [| exact VI'].
      (first [ dand6 VI' as Q1 Q2 Q3 Q3b Q4 Q5 | destruct VI' as (Q1 & Q2 & Q3 & Q3b & Q4 & Q5) ]). (first [ pose proof ((D_AI ltac:(discriminate) ltac:(discriminate))) as dR_16; dand4 dR_16 as NIA NIB NBA NBB | destruct (D_AI ltac:(discriminate) ltac:(discriminate)) as (NIA & NIB & NBA & NBB) ]).
      unfold oibuf in NBA, NBB, D_IBV. rewrite EVI in NBA, NBB, D_IBV.
      refine (conj Q1 (conj _ (conj Q3 (conj Q3b (conj Q4 I))))).
      assert (HCi : hcover A [x_v x Finclude_src; vb_buf yi] Vd).
      { intros a [X|[X|X]].
        - eapply hcover_blk; [exact LAS| wz_not_in| exact X].
        - eapply hcover_blk; [exact LAB| wz_not_in| exact X].
        - eapply hcover_rng; [exact LVEP| wz_not_in| clear - X; lia]. }
      eapply (vsb_obj_call (pe_H E) A A1 m m1 md (pe_sp E) DESTROY_STACK Vd nowhere [x_v x Finclude_src; vb_buf yi] AINV CF HG WIN);
        [exact (hcover_vcover (pe_H E) _ _ _ HCi)| in_list| in_list
        | apply LK; [exact (proj1 (proj2 (proj2 Q2)))| exact NIA| exact NIB]
        | apply LK; [exact (proj1 (proj2 (proj2 (proj2 Q2))))| exact NBA| exact NBB]
        | exact Q2]. }
    assert (AVA : avoids_call (pe_sp E) DESTROY_STACK Vd (pe_VEP E) 224).
    { split; [left; revert VEPhi WIN; clear; intros; lia|].
      intros i Hi X. subst Vd. cbn beta in X. unfold blk in X. revert Hi X DXA DXB. clear. intros; lia. }
    assert (AVB : avoids_call (pe_sp E) DESTROY_STACK Vd (pe_VEP E + 232) 80).
    { split; [left; revert VEPhi WIN; clear; intros; lia|].
      intros i Hi X. subst Vd. cbn beta in X. unfold blk in X. revert Hi X DXA DXB. clear. intros; lia. }
    apply (rw_cells_ccall LayoutP0 A A1 (pe_sp E) DESTROY_STACK Vd nowhere m m1 CF (pe_VEP E)) in VA;
      [| eapply crange_block; [exact AINV| exact LVEP| clear; lia| clear; cbn; lia| clear; cbn; lia] | cbn [cells_size csize Nat.add length]; exact AVA].
    apply (rw_cells_ccall LayoutP0 A A1 (pe_sp E) DESTROY_STACK Vd nowhere m m1 CF (pe_VEP E + 232)) in VB;
      [| eapply crange_block; [exact AINV| exact LVEP| clear; lia| clear; cbn; lia| clear; cbn; lia]
       | cbn [cells_size csize Nat.add length]; exact AVB].
    assert (VEPC1 : rw_cells rsegs m1 (pe_VEP E) (vep_cells (fupd v' Fattr_vsb 0) (x_tag x) (x_q x))).
    { rewrite <- pd_cells_attr_vsb. unfold vep_cells. cbn [firstn skipn].
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (pd_join3 rsegs m1 (pe_VEP E) pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VB| cbn [cells_size csize Nat.add length]; clear; lia]. }
    clear VA VB PSC AVA AVB.
    assert (HS : forall p st, hstep E (PST p st v' (x_tag x) (x_q x) (x_vv x) (Some y) (x_vi x))
                                (PST p st (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A A1 m m1).
    { intros p st.
      eapply (hstep_call0 E _ _ A A1 m m1 DESTROY_STACK Vd);
        [ exact CF
        | clear; unfold DESTROY_STACK; unfold_stacks_g; lia
        | eapply parse_window_mapped; [exact PE| exact ST1| exact FR1]
        | intros a [X|[X|X]]; unfold pzone; cbn [x_v x_va x_vi x_vv]; rewrite ?EAV;
          [ right; right; right; left; left; exact X
          | right; right; right; left; right; exact X
          | left; unfold blk; split; [clear - VEPlo; lia| clear - X; lia] ]
        | intros p0 k Hp NB; apply LK; [exact Hp| |]; intros ->; apply NB; unfold pst_blocks; cbn [x_v x_va x_vi x_vv]; rewrite ?EAV; right; left; [left|right]; reflexivity
        | unfold pst_blocks; psimp; rewrite ?EIS; intros p0 [Hp|[Hp|Hp]]; [left; left; exact Hp| destruct Hp| left; right; right; exact Hp]
        | unfold parse_new, pzone; psimp; rewrite ?EAV, ?EIS; cbn [option_map]; intros a [Ha|[Ha|Ha]];
          [ right; right; left; exact Ha | destruct Ha | right; right; right; right; left; destruct (x_vi x); [exact Ha| destruct Ha] ] ]. }
    unfold loop_ms in K. rewrite EVA in K.
    assert (LB1 : a_livebytes A1 = pe_LB0 E - 56 + pw_bytes (x_vv x) None (x_vi x)) by (rewrite LBd, LB; rewrite ?EVA, ?EYS; unfold pw_bytes; clear; lia).
    assert (NL1 : a_nlive A1 = pe_NL0 E + pw_nlive None (x_vi x)) by (rewrite NLd, NL; rewrite ?EVA; unfold pw_nlive; clear; lia).
    exact (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 m1 md1 AINV1 MI1 MDF ST1 FR1 VEPC1 IMG1 HENV1 DATA1 VSBO1 WAL1 LVEP1 VI1 LB1 NL1 HS).
  Qed.
End S.
