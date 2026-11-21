(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec Atomics.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8SRKit XA_leaves XL_mutex XL_cond X8_A_leaves2 X8_stream_stmt X8_S_kit X8_S_vec.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Store.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Win.
Local Ltac stack0_via_aapp ::= stack0_via_aapp_fast.
Local Ltac aconst_via_aapp ::= aconst_via_aapp_fast.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8Kit2.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Keyed Unification.   (* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 Set StepFast.sf_check := true.   (* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
Scheme kc__1 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.

(* The side facts carried across a call: ACONST, the stack window, the statement's
   accessible block and the impl block, transported along one munch.  A Lemma and
   not an [assert] because the [Local Ltac]s below name it - see the note in
   [state_remove_spec]. *)
Lemma sr_side : forall W m mc lo shi stb implb,
  ACONST m -> stack0 m lo shi -> accessible m stb 312 -> addressable m implb 96 ->
  munch W m mc -> wmono asegs m mc -> Forall awin W ->
  ALOWSH_LO <= sh implb -> sh implb + 12 <= AHI_LO ->
  ACONST mc /\ stack0 mc lo shi /\ accessible mc stb 312 /\ addressable mc implb 96.
Proof.
  intros W mx mc lx hx sx ix ACx SKx ASx ADx MUx WMx FWx SHL SHH.
  assert (SD : aside mx lx hx [(sx, 312)] []).
  { split; [exact ACx| split; [exact SKx| split]].
    - constructor; [exact ASx| constructor].
    - constructor. }
  destruct (aside_transport _ _ _ _ _ _ _ SD MUx WMx FWx) as (ACc & SKc & ASs & _).
  split; [exact ACc| split; [exact SKc| split; [exact (Forall_inv ASs)|]]].
  eapply addressable_transport; [exact ADx| exact MUx| exact WMx|].
  change (disjoint_from W (sh ix) 12).
  apply awin_disjoint_shland; assumption.
Qed.

Lemma state_remove_spec : state_remove_stmt.
Proof.
  (* The Sc success arm is unchanged, but the replay's congruence motive
     contains the old failure arm. Execute the walk against the current model. *)
  assert (VEC1 : forall m vb x n junk,
    rw_cells asegs m vb [CB (8 * length [x]) (flat_map le8z [x]); CB n junk] ->
    rw_cells asegs m vb [C8 (wz x); CB n junk]).
  { intros mx vx x nx junkx C. eapply rw_cells_reshape; [exact C| |].
    - destruct C as [[WF _] _]. cbn [cells_wf cell_wf] in WF |- *.
      destruct WF as (_ & WJ & _). split; [exact I| split; [exact WJ| exact I]].
    - cbn [cells_bytes cbytes flat_map]. unfold le8z. rewrite !app_nil_r. reflexivity. }
  assert (VEC0 : forall m vb x n junk vcap,
    rw_cells asegs m vb [C8 (wz x); CB n junk] -> (8 + n)%nat = Z.to_nat (8 * vcap) ->
    rw_cells asegs m vb [CB (8 * length (@nil Z)) (flat_map le8z []);
      CB (Z.to_nat (8 * (vcap - zlength (@nil Z)))) (le8z x ++ junk)]).
  { intros mx vx x nx junkx cap C E. eapply rw_cells_reshape; [exact C| |].
    - destruct C as [[WF _] _]. cbn [cells_wf cell_wf] in WF |- *.
      destruct WF as (_ & WJ & _). split; [reflexivity| split; [|exact I]].
      unfold zlength. cbn [length Z.of_nat]. rewrite Z.sub_0_r, length_app, WJ.
      unfold le8z. rewrite length_le8. exact E.
    - cbn [cells_bytes cbytes flat_map app]. unfold le8z. rewrite !app_nil_r. reflexivity. }
  assert (CAPN : forall cap, 1 <= cap ->
    (8 + Z.to_nat (8 * (cap - 1)))%nat = Z.to_nat (8 * cap)).
  { intros cap HC. replace (8 + Z.to_nat (8 * (cap - 1)))%nat
      with (Z.to_nat (8 + 8 * (cap - 1))).
    - f_equal. ring.
    - rewrite Z2Nat.inj_add by (clear - HC; lia). reflexivity. }
  assert (C8EQ : forall a b c a' b' c' : word, a = a' -> b = b' -> c = c' ->
    cells_bytes [C8 a; C8 b; C8 c] = cells_bytes [C8 a'; C8 b'; C8 c']).
  { intros a b c a' b' c' -> -> ->. reflexivity. }
  (* [sr_side] was here, as [assert (SIDE : ...)].  It cannot be: [sr_refresh]
     below is a [Local Ltac] whose body contains [destruct (SIDE ...)], and a
     constr in an Ltac body is resolved when the tactic is DEFINED, not when it
     runs - so a proof-local hypothesis is not in scope for it, which is what
     a farm round answered at :103 with "The reference SIDE was
     not found in the current environment".  It is now a section-level Lemma
     above, which is exactly the shape the twin file already uses: Bo's
     [spw_side] (Bo/X8_S_remove.v:62) is a top-level Lemma for the same reason,
     consumed by its own Local Ltacs at :96 and :104. *)
  Local Ltac sr_kill K :=
    exfalso; first [ revert K; rewrite ?unsigned_lit by lia; lia
                  | vm_compute in K; discriminate
                  | vm_compute in K; exact (K eq_refl)
                  | vm_compute in K; lia ].
  Local Ltac sr_nt := let K := fresh "K" in if_cases K; zify_cond K; [sr_kill K|clear K].
  Local Ltac sr_tk := let K := fresh "K" in if_cases K; zify_cond K; [clear K|sr_kill K].
  Local Ltac sr_even := first [rewrite unsigned_lit by lia; reflexivity|vm_compute; reflexivity].
  Local Ltac sr_refresh :=
    lazymatch goal with
    | MUx : munch ?W ?mx ?mc, WMx : wmono asegs ?mx ?mc, FWx : Forall awin ?W,
      ACx : ACONST ?mx, SKx : stack0 ?mx ?lx ?hx,
      ASx : accessible ?mx ?sx 312, ADx : addressable ?mx ?ix 96
      |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      let ACc := fresh "ACc" in let SKc := fresh "SKc" in
      let ASc := fresh "ASc" in let ADc := fresh "ADc" in
      destruct (sr_side W mx mc lx hx sx ix ACx SKx ASx ADx MUx WMx FWx
        ltac:(lia) ltac:(lia)) as (ACc & SKc & ASc & ADc)
    end.
  Local Ltac sr_rd A n g :=
    sr_refresh;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      let RD := fresh "RD" in
      pose proof (accessible_read0_sr mc A n g
        ltac:(first [assumption|eapply addressable_accessible; [eassumption|lia|lia|lia]])
        ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as RD
    end.
  Local Ltac sr_reload :=
    lazymatch goal with RD : ov_read_bytes _ _ _ 1 = _ |- _ =>
      step; clear RD;
      try replace (zxb (b8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity);
      try replace (sxb (b8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity);
      shchk_br
    end.
  Local Ltac sr_full :=
    lazymatch goal with RD : ov_read_bytes _ _ _ 1 = _ |- _ => shchk_fast RD end.
  Local Ltac sr_word := first [reflexivity|apply Z_to_bv_eqm;
    rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia].
  unfold state_remove_stmt, ASTATE_REMOVE_STACK, P_A_STATE_REMOVE.
  intros stb implb vb w i vcap lo shi LB ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    RO S16 APS IB SEP1 SEP2 SEP3 VCAP ST LO CE SP16 RA MI AC SK SPHI ACS.
  unfold impl_one in IB.
  destruct (AImplBlockC_open _ _ _ _ IB)
    as (p & j7 & IN & RB & CH & OK & EV & PM & VC & LE & VS & ADI). clear IB.
  cbn [im_hdr im_lk im_vb im_states im_vcap] in *.
  change (zlength [stb + 32]) with 1 in *.
  destruct VS as [[V0 _]|(q & junk & INQ & RBV & POS & VCELLS & SHV)]; [exfalso; lia|].
  apply VEC1 in VCELLS.
  unfold SpcHdrCells in CH. cbn [spc_vptr spc_use spc_weak spc_init] in CH.
  destruct PM as (PMC & _ & PAL). unfold PMutexCells, zeros in PMC. cbn [repeat] in PMC.
  unfold SZ_SPCI_IMPL, SZ_SPCI_STATE, AINTRIN_STACK, rm_W, wz in *.
  pose proof aceil_facts as (AF1 & AF2 & AF3).
  pose proof (bv_unsigned_in_range 64 sp) as SPB.
  unfold bv_modulus in SPB. change (2 ^ Z.of_N 64) with (2^64) in SPB.
  pose proof (rblock_bounds _ _ RB) as (IB0 & _ & IBHI & IBIMG & IBCE & IB8).
  pose proof (rblock_bounds _ _ RBV) as (VB0 & _ & VBHI & VBIMG & VBCE & VB8).
  pose proof RB as (IBPOS & IB16 & _ & API & _).
  pose proof RBV as (VBPOS & VB16 & _ & APV & _).
  pose proof (aapp_not_shadowland _ _ API) as APISEP.
  pose proof (aapp_not_shadowland _ _ APV) as APVSEP.
  pose proof (aapp_not_shadowland _ _ APS) as APSSEP.
  (* At :194 (first [sr_full]): the load's shadow address came out as
     [((stb + 96) mod 2^64) >> 3 + 0x7fff8000] while RD states [(stb + 96) >> 3 + 0x7fff8000].
     [zsimp] drops the wrap only when [zrange]'s lia sees [0 <= e < 2^64], and stb's bounds sat
     behind [aapp] (APS) and [aceil]; implb's and vb's behind [AAPP_HI].  State them as literals
     so every later [zstep] keeps these addresses unwrapped. *)
  assert (STBB : 0 <= stb /\ stb + 312 <= 140737488355328).
  { pose proof APS as APS'. destruct APS' as [[X1 X2]|[X1 X2]];
      cbv [AIMG_TOP ALOWSH_LO AHI_LO] in X1, X2; lia. }
  assert (IMPB : implb + 96 <= 140737488355328).
  { change AAPP_HI with 140737488355328 in IBHI. lia. }
  assert (VBB : vb + 8 * vcap <= 140737488355328).
  { change AAPP_HI with 140737488355328 in VBHI. lia. }
  assert (SHIB : ALOWSH_LO <= sh implb /\ sh implb + 12 <= AHI_LO).
  { unfold sh, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *.
    clear - IB0 IBHI. Z.div_mod_to_equations. lia. }
  assert (SHVB : ALOWSH_LO <= sh vb /\ sh vb + vcap <= AHI_LO).
  { unfold sh, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *.
    clear - VB0 VBHI POS. Z.div_mod_to_equations. lia. }
  assert (AMO : amo_aligned AW (Z_to_bv 64 (implb + 8)) = true).
  { apply amo_aligned_intro; [clear - IB0 IBHI; unfold AAPP_HI in *; lia|].
    clear - IB8. Z.div_mod_to_equations. lia. }
  pose proof (munch_refl [(lo, bv_unsigned sp); (implb + 8, implb + 12);
    (implb + 32, implb + 72); (implb + 80, implb + 88); (vb, vb + 8)]%Z m) as MUA.
  pose proof (wmono_refl asegs m) as WMA.
  assert (FW : Forall awin [(lo, bv_unsigned sp); (implb + 8, implb + 12);
    (implb + 32, implb + 72); (implb + 80, implb + 88); (vb, vb + 8)]%Z).
  { repeat apply Forall_cons;
      [apply awin_stack; exact CE
      |eapply awin_aapp; [exact API|lia|lia]
      |eapply awin_aapp; [exact API|lia|lia]
      |eapply awin_aapp; [exact API|lia|lia]
      |eapply awin_aapp; [exact APV|lia|lia]
      |apply Forall_nil]. }
  rename AC into BASEAC. rename SK into BASESK.
  rename ACS into BASEACS. rename ADI into BASEADI.
  pose proof (ACONST_shbase _ BASEAC) as [G1 G2].
  unfold AGOT_SHBASE, ASHBASE_CELL, wz in G1, G2. rewrite ASHADOW_BASE_val in G2.
  carve_frame 48%nat ST.
  (* cb758-cb77c: prologue, shadow-base load, and first frame slot. *)
  do 9 step. st1.
  step. sr_rd stb 312 (stb + 96). sr_full.
  step. step. step. sr_nt.
  step. sr_rd implb 96 (implb + 8). sr_full.
  step. rewrite ?sx32_lit by lia. step. sr_nt.
  step. step. step.
  sr_rd implb 96 (implb + 8). sr_reload.
  st1. st1. rewrite ?sx32_lit by lia.
  (* cb7d8-cb7e8: the lr/sc pair succeeds; no retry or failure-arm store. *)
  amo_step AMO. rewrite ?sx32_lit by lia.
  step. sr_nt. amo_step AMO. step. sr_nt. step. sr_tk.
  step. step. sr_nt.
  sr_rd stb 312 (stb + 88). sr_full.
  step. st1. step. sr_tk.
  step. step.
  sr_refresh.
  pose proof (sp_arrow_spec_at P_A_SP_IMPL_ARROW (or_intror eq_refl)) as SPA.
  unfold sp_arrow_stmt, P_A_SP_IMPL_ARROW, SP_ARROW_STACK, wz in SPA.
  callZ (SPA (bv_unsigned sp + -48) (implb + 32) lo);
    [lazymatch goal with FRc : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ =>
       pose proof (rw_cells_ro_cell _ _ _ _ 0%nat _ FRc eq_refl) as RO0;
       cbn [Z.of_nat] in RO0; rewrite Z.add_0_r in RO0; exact RO0 end
    |lia|lia|rewrite ?unsigned_lit by lia; eassumption
    |rewrite ?unsigned_lit by lia; lia|lia
    |left; rewrite ?unsigned_lit by lia; lia|sr_even|assumption|assumption
    |eapply stack0_accessible; [eassumption|lia|lia|rewrite ?unsigned_lit by lia; lia]
    |clear - SP16; Z.div_mod_to_equations; lia|].
  clear SPA. unfold wz in *.
  step. step. sr_refresh.
  pose proof mtx_lock_spec as MLK.
  unfold mtx_lock_stmt, mtx_lock_post, P_A_MTX_LOCK, MTX_LOCK_STACK, wz in MLK.
  callZ (MLK (implb + 32) lo);
    [split; [unfold PMutexCells, zeros; cbn [repeat]; eassumption|split; [left; reflexivity|exact PAL]]
    |rewrite ?unsigned_lit by lia; eassumption
    |rewrite ?unsigned_lit by lia; lia|lia|left; lia|sr_even|assumption|].
  unfold wz in *.
  lazymatch goal with HP : APMutex _ _ EBUSY |- _ =>
    destruct HP as (PMC2 & _ & _); unfold PMutexCells, zeros in PMC2; cbn [repeat] in PMC2 end.
  (* cb818-cb8b8: find the sole vector element, keep it, and shorten the vector. *)
  step. sr_rd implb 96 (implb + 80). sr_full.
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (SHVC : SHAD mc vb (cc_shadow (8 * vcap) 8))
      by (eapply SHAD_transport; [exact SHV|exact MUA|exact WMA|];
          rewrite cc_shadow_length' by (clear - POS; Z.div_mod_to_equations; lia);
          replace (8 * vcap / 8) with vcap by (clear; lia);
          apply awin_disjoint_shland; [exact FW|lia|lia]) end.
  (* At :255 "The reference vb was not found": an Ltac body is
     globalised where it is DEFINED, so it cannot name the proof's own variables and
     hypotheses.  They are passed as arguments instead. *)
  Local Ltac sr_vec_rd vb vcap SHV MUA WMA FW POS :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      let SHC := fresh "SHC" in let RD := fresh "RD" in
      assert (SHC : SHAD mc vb (cc_shadow (8 * vcap) 8))
        by (eapply SHAD_transport; [exact SHV|exact MUA|exact WMA|];
            rewrite cc_shadow_length' by (clear - POS; Z.div_mod_to_equations; lia);
            replace (8 * vcap / 8) with vcap by (clear; lia);
            apply awin_disjoint_shland; [exact FW|lia|lia]);
      pose proof (cc_shadow_rd0 mc vb (8 * vcap) 8 SHC ltac:(lia) ltac:(lia)) as RD
    end.
  sr_vec_rd vb vcap SHV MUA WMA FW POS. sr_full.
  step. sr_rd implb 96 (implb + 72). sr_full.
  step. step. step. step. sr_nt.
  step. step. step. step. sr_vec_rd vb vcap SHV MUA WMA FW POS.
  (* At :268 (sr_reload): the goal's load address is
     [2147450880 + bv_unsigned (Z_to_bv 64 vb) >> 3] while RD reads [vb >> 3 + 2147450880] -
     an unreduced wrap and a commuted sum (the round printed both).  sr_reload's [step]
     matches syntactically, so put both in one form first: drop the wrap in the goal
     (0 <= vb from VB0, the upper bound from VBB) and commute RD's sum. *)
  try rewrite (unsigned_lit vb) by lia.
  match goal with RDx : ov_read_bytes _ _ _ 1 = _ |- _ => try rewrite (Z.add_comm (Z.shiftr vb 3)) in RDx end.
  sr_reload.
  step. step. sr_tk.
  sr_vec_rd vb vcap SHV MUA WMA FW POS. sr_full. step.
  sr_rd implb 96 (implb + 80). sr_reload.
  step. step. step. step. step.
  (* Only annotate writes shadow. Until this point MUA has five awin windows;
     enlarge it once, before the call, rather than pretending its shadow window is awin. *)
  sr_refresh.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (SHVA : SHAD mc vb (cc_shadow (8 * vcap) 8))
      by (eapply SHAD_transport; [exact SHV|exact MUA|exact WMA|];
          rewrite cc_shadow_length' by (clear - POS; Z.div_mod_to_equations; lia);
          replace (8 * vcap / 8) with vcap by (clear; lia);
          apply awin_disjoint_shland; [exact FW|lia|lia]);
    assert (MU : munch (rm_W lo sp implb vb vcap) m mc)
      by (eapply munch_weaken; [|exact MUA]; unfold sub_fp, rm_W; cbn [outside]; intros; tauto)
  end.
  pose proof WMA as WM. clear MUA.
  pose proof (@annotate_vec_spec HCEIL H HH P_A_VEC_STATEP_ANNOT_SHRINK
    ltac:(right; left; reflexivity)) as ANN.
  unfold annotate_vec_stmt, annot_old, annot_new, P_A_VEC_STATEP_ANNOT_SHRINK,
    P_A_VEC_STATEP_ANNOT_DELETE, P_A_VEC_STATEP_ANNOT_NEW, AANNOTATE_VEC_STACK, AINTRIN_STACK, wz in ANN.
  cbn [Z.eqb Pos.eqb] in ANN.
  (* At :299: the walk leaves a1 as
     [Z_to_bv 64 (bv_signed (Z_to_bv 64 (vb + 8 + - bv_unsigned (Z_to_bv 64 vb))) >> 3)]
     (the element count, unreduced), where annotate's spec is applied at k = 1.
     Bring a1 to that literal first, as :274 does for the shadow address. *)
  try rewrite (unsigned_lit vb) by lia.
  try replace (vb + 8 + - vb) with 8 by lia.
  try replace (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 8)) 3)) with (Z_to_bv 64 1)
    by (apply bv_eq; vm_compute; reflexivity).
  eapply evt_cut; [eapply (ANN (implb + 72) vb vb vcap 1 lo)|].
  all: try solve [rewrite ?unsigned_lit by lia; first [assumption|lia|left; lia|right; lia]].
  all: try solve [lazymatch goal with |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => sr_even end].
  all: try solve [lazymatch goal with
    | CV : rw_cells asegs ?mc (implb + 72) _ |- ro_cells asegs ?mc (implb + 72) ?cs =>
      assert (CV' : rw_cells asegs mc (implb + 72) cs)
        by (eapply rw_cells_reshape; [exact CV|cbn; repeat split|];
            unfold wz; apply C8EQ; sr_word);
      exact (proj1 CV')
    end].
  (* The one side goal the closer above leaves (from a probe round):
     [ro_cells asegs m5 (implb + 72) [C8 vb; C8 vb; C8 (vb + 8 * vcap)]], with the
     hypothesis [rw_cells asegs m5 (implb + 72)] over the same three cells; [ro_cells] is
     [rw_cells]' first conjunct ([Lib/Step.v]). *)
  all: try solve [match goal with
    | CV : rw_cells asegs ?mc ?A _ |- ro_cells asegs ?mc ?A _ => exact (proj1 CV)
    end].
  all: try solve [lazymatch goal with |- SHAD _ _ (cc_shadow _ ?d) =>
                    replace d with 8 by lia; exact SHVA end].
  all: try solve [eapply addressable_accessible; [eassumption|lia|lia|lia]].
  all: try solve [clear - IB8 VB8; Z.div_mod_to_equations; lia].
  (* Destructure annotate's post explicitly: keep its munch long enough to
     carry stack0 and the implementation's addressability past the shadow write. *)
  intros ms' PO. unfold annotate_vec_post in PO.
  rewrite ?unsigned_lit in PO by lia. rewrite ?Z.add_0_r in PO.
  destruct_exs PO.
  destruct PO as (E & MUann & WMann & MIann & STann & SHVann & ACann). subst ms'.
  lazymatch type of MUann with munch _ ?mb ?ma =>
    assert (SKann : stack0 ma lo shi)
      by (eapply stack0_transport; [eassumption|exact MUann|exact WMann|];
          constructor; [apply stack0_ok_app; cbn; unfold AHI_LO; lia|];
          constructor; [apply stack0_ok_sh'; lia|constructor]);
    assert (ADIann : addressable ma implb 96)
      by (eapply addressable_transport; [eassumption|exact MUann|exact WMann|];
          change (disjoint_from [(lo, bv_unsigned sp + -48);
            (sh vb, sh vb + vcap)]%Z (sh implb) 12);
          cbn [disjoint_from]; split; [left; lia|split; [|exact I]];
          unfold sh; rewrite ASHADOW_BASE_val;
          clear - SEP3 IB8 VB8; Z.div_mod_to_equations; lia);
    assert (ACSann : accessible ma stb 312)
      by (eapply accessible_transport_fr with (ff := vb) (k := vcap);
          [eassumption|exact MUann|
           constructor; [unfold win_fr; cbn; right; left; unfold AHI_LO; lia|];
           constructor; [unfold win_fr; cbn; right; right; lia|constructor]
          |lia|exact VB8|lia|exact SEP2]);
    (* [transport_after_call]'s footprint check ([cbn [outside]; slia]) cannot see through
       [rm_W]: MU's footprint is unfolded from here on (this call and mtx_unlock's); the
       post's [munch (rm_W ..)] takes it by conversion at [finish] *)
    unfold rm_W in MU;
    (* the frame at sp - 48 is apart from annotate's shadow window: the shadow ends below
       AHI_LO, far below the stack ([aceil_facts]); stated so the transport's [slia] keeps it *)
    assert (SHSP : sh vb + vcap <= bv_unsigned sp + -48)
      by (destruct SHVB as [_ SHV2]; unfold AHI_LO in SHV2; lia);
    transport_after_call asegs mb ma MUann WMann;
    clear MUann WMann;
    clear BASEAC BASESK BASEACS BASEADI WMA;
    rename ACann into BASEAC; rename SKann into BASESK;
    rename ACSann into BASEACS; rename ADIann into BASEADI;
    pose proof (munch_refl [(lo, bv_unsigned sp); (implb + 8, implb + 12);
      (implb + 32, implb + 72); (implb + 80, implb + 88); (vb, vb + 8)]%Z ma) as MUA;
    pose proof (wmono_refl asegs ma) as WMA
  end.
  replace (vb - vb) with 0 in SHVann by lia.
  try lazymatch goal with
    |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?npc)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 npc)) with (Z_to_bv 64 npc)
        by (symmetry; apply ret_pc_even; [lia|reflexivity])
  end.
  unfold wz in *.
  (* cb8cc-cb8f8: unlock, release the temporary shared reference, and return. *)
  step. step.
  pose proof mtx_unlock_spec as MUL.
  unfold mtx_unlock_stmt, mtx_unlock_post, P_A_MTX_UNLOCK, MTX_UNLOCK_STACK, wz in MUL.
  callZ (MUL (implb + 32) lo);
    [split; [unfold PMutexCells, zeros; cbn [repeat]; eassumption|split; [right; reflexivity|exact PAL]]
    |rewrite ?unsigned_lit by lia; eassumption
    |rewrite ?unsigned_lit by lia; lia|lia|left; lia|sr_even|assumption|].
  clear MLK MUL ANN. unfold wz in *.
  lazymatch goal with HP : APMutex _ _ 0 |- _ =>
    destruct HP as (PMC3 & _ & _); unfold PMutexCells, zeros in PMC3; cbn [repeat] in PMC3 end.
  step. step. sr_nt. step.
  sr_rd implb 96 (implb + 8). sr_full.
  step. amoadd_step AMO. step. step. sr_tk.
  step. step. step. step.
  lazymatch goal with FRc : rw_cells _ _ (bv_unsigned sp + -48) _, STc : stk _ _ lo _ |- _ =>
    release_frame FRc STc (bv_unsigned sp) end.
  step. step. sr_refresh.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (SHV0 : SHAD mc vb (cc_shadow (8 * vcap) 0))
      by (eapply SHAD_transport; [exact SHVann|exact MUA|exact WMA|];
          rewrite cc_shadow_length' by (clear - POS; Z.div_mod_to_equations; lia);
          replace (8 * vcap / 8) with vcap by (clear; lia);
          apply awin_disjoint_shland; [exact FW|lia|lia])
  end.
  finish.
  all: lazymatch goal with
    | |- AImplBlockC _ _ _ _ =>
      unfold impl_none; eapply AImplBlockC_close; cbn [im_hdr im_lk im_vb im_states im_vcap];
      [exact IN
      |exact RB
      |unfold SpcHdrCells; cbn [spc_vptr spc_use spc_weak spc_init]; eassumption
      |exact OK
      |first [exact EV|reflexivity]
      |split; [unfold PMutexCells, zeros; cbn [repeat]; eassumption|split; [left; reflexivity|exact PAL]]
      |eapply rw_cells_reshape; [eassumption|cbn; repeat split|];
       unfold wz, zlength; cbn [length Z.of_nat]; apply C8EQ; sr_word
      |unfold zlength; cbn [length Z.of_nat]; lia
      |right; exists q, (le8z (stb + 32) ++ junk);
       split; [exact INQ|split; [exact RBV|split; [exact POS|split;
         [eapply VEC0; [eassumption|apply CAPN; lia]|exact SHV0]]]]
      |assumption]
    end.
Qed.

End HCW.
