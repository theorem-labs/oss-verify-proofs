(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDeq OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhASlotKB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount.UbMhCountSpec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDeq OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.UbMhASpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhASlotW2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section ASF.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M : mem) (mdl : Model)
            (regs : bvmap 5 word) (rom : word -> option byte) (sp sc req : Z) (Q : config -> Prop) (d : nat).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HLG : LEDGER st (m_vmmaps mdl).
  Hypothesis NJ : nojunk st.
  Hypothesis Hh : m_halted mdl = None.
  Hypothesis Hlz : m_vm_lazy mdl = [].
  Hypothesis Hmat : m_vm_materialized mdl = [].
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hd : dle (dbound (16 * size_class sc)) d.
  Hypothesis Hlimbo : zlen (s_limbo st) + Z.of_nat d + 1 <= 8.
  Hypothesis Hreq : 0 <= req /\ req + 4 <= 16 * size_class sc.
  Hypothesis HBUD : PHI L + MBASE <= vm_limit (m_vmmaps mdl).
  Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 req.
  Hypothesis R2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis Rra : ret_ok (getr regs 1).
  Hypothesis Hsp : CEIL + ASSTK d <= sp /\ sp < 2 ^ 64.
  Hypothesis DEF : defined M (sp - ASSTK d) sp.
  Hypothesis HQ : forall c', as_ok st L sc req d sp regs M mdl rom c' -> Q c'.
  Hypothesis IHd : forall d', (d' < d)%nat -> AS_SPEC3 d'.

  #[local] Notation PT := (pt st L M mdl regs sp sc d).

  Let LE := (L_E st L M mdl regs rom sp sc req Q d R2 Rra Hsp HQ).
  Let LT := (L_T st L M mdl regs rom sp sc req Q d Hsc Hreq R2 Rra Hsp HQ).
  Let LA5 := (L_A5 st L M mdl regs rom sp sc req Q d Hsc Hreq R2 Rra Hsp HQ).
  (* [comment removed for export] *)
  Hypothesis LG : forall s1 Mc mdl1 r,
    PT s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st -> s_alist s1 sc = [] -> getr r 18 = Z_to_bv 64 req ->
    kat RSEGS (mkCfg (mkst r (0x67490%bv : word) Mc rom) mdl1) Q.
  (* [comment removed for export] *)
  Hypothesis LGa : forall s1 Mc mdl1 r,
    PT s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st -> s_alist s1 sc = [] -> getr r 18 = Z_to_bv 64 req -> agf s1 ->
    kat RSEGS (mkCfg (mkst r (0x67490%bv : word) Mc rom) mdl1) Q.

  (* [comment removed for export] *)
  Lemma L_A3 : forall s1 Mc mdl1 r g rest,
    PT s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st ->
    s_alist s1 sc = g :: rest -> mr_avail (s_meta s1 g) = 0 ->
    getr r 12 = Z_to_bv 64 g -> getr r 18 = Z_to_bv 64 req ->
    kat RSEGS (mkCfg (mkst r (0x67324%bv : word) Mc rom) mdl1) Q.
  Proof.
    intros s1 Mc mdl1 r g rest P NJ1 EL Hl Hav0 A12 A18.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    destruct (member_facts L sc s1 g W1 ltac:(rewrite Hl; left; reflexivity)) as (Hg & Hgsc & Ug & Glo & Ghi).
    pose proof (wG_each s1 L (WF_groups s1 L W1) g Hg) as WG. pose proof (wg_frr s1 L g WG) as FRR.
    destruct (G_meta_cells s1 L Mc W1 RP1 g Hg) as (ar1 & k1 & _ & _ & _ & _ & _ & _ & G8 & RM1 & _ & _).
    destruct RM1 as [Rpv Rnx Rme Rav Rfr RW]. rewrite Hav0 in Rav.
    pose proof (ctx_store_ok s1 Mc RP1) as SOKc.
    assert (SOKa : store_ok RSEGS Mc (Z_to_bv 64 (ctx_active sc)) 8%nat = true) by (unfold ctx_active, CTX in *; sok 928%nat SOKc).
    destruct (next_of_head L sp sc req d Hsc Hreq Hsp s1 g rest W1 Hl) as (SELF & IN & NE).
    destruct (Z.eq_dec (mr_freed (s_meta s1 g)) 0) as [FR0|FRNZ].
    - (* [comment removed for export] *)
      pose proof (meta_store_ok s1 L Mc W1 RP1 g Ug) as SOKg.
      assert (SOK16 : store_ok RSEGS Mc (Z_to_bv 64 g) 16%nat = true) by (ceil; unfold HEAPLO in *; sok 40%nat SOKg).
      rewrite FR0 in Rfr.
      assert (Hinl : UbMhDeq.inl s1 g = true) by (apply (proj2 (UbMhDeq.inl_true s1 g)); rewrite Hgsc, Hl; left; reflexivity).
      destruct rest as [|nx0 rest'].
      + (* [comment removed for export] *)
        assert (Enx : mr_next (s_meta s1 g) = g) by (apply (proj2 SELF); reflexivity).
        destruct (aDeqS Mc sc g (mr_next (s_meta s1 g)) Hsc ltac:(unfold HEAPLO in *; lia) ltac:(rewrite Enx; unfold HEAPLO in *; lia) Rfr Rnx SOKa SOK16
                    r rom A12 Q21 Enx) as (r' & RUN & E10 & K').
        eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
        set (M' := m_deqS Mc sc g) in *.
        assert (G' : mem_grows Mc M') by (unfold M', m_deqS; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
        assert (W' : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) -> (g <= a < g + 16) \/ (ctx_active sc <= a < ctx_active sc + 8)).
        { intros a Ha NEa. ceil; unfold M', m_deqS, ctx_active, CTX, HEAPLO in *. wdiff2 NEa Mc a. }
        assert (Hmulti : UbMhDeq.multi s1 g = false).
        { destruct (UbMhDeq.multi s1 g) eqn:E; [|reflexivity]. exfalso. apply (proj1 (UbMhDeq.multi_nxt s1 L g W1 Hinl) E). exact Enx. }
        destruct (deq_close s1 L Mc M' g (spc sp d) W1 RP1 Hg Hav0 FR0 (spc_ok sp d Hsp)
                    ltac:(intros a Ha NEa; unfold UbMhDeq.d_wr; destruct (W' a Ha NEa) as [A|A]; [right; left; split; [exact Hinl | exact A] | right; right; right; split; [exact Hinl | rewrite Hgsc; exact A]])
                    G' ltac:(ceil; unfold M', m_deqS, HEAPLO, ctx_active, CTX in *; cellw) ltac:(ceil; unfold M', m_deqS, HEAPLO, ctx_active, CTX in *; cellw)
                    ltac:(rewrite Hmulti; intros X; discriminate X) ltac:(rewrite Hmulti; intros X; discriminate X)
                    ltac:(intros _; rewrite Hgsc; unfold UbMhDeq.l'; rewrite Hgsc, Hl, (zremove_head g [] ltac:(intros [])); cbn [head_of];
                          ceil; unfold M', m_deqS, HEAPLO, ctx_active, CTX in *; cellw)) as [W2 RP2].
        pose proof (deq_facts s1 g) as (AL2 & ALo & _ & SL2 & GR2 & AI2 & MT2). rewrite Hgsc in AL2, ALo.
        set (s2 := UbMhDeq.st' s1 g) in *.
        assert (P2 : PT s2 M' mdl1 r').
        { apply (pt_step st L M mdl regs sp sc req d Hsc Hreq Hsp s1 Mc mdl1 r s2 M' r' P W2 RP2 eq_refl eq_refl eq_refl eq_refl).
          - intros k Hk. apply ALo. lia.
          - intros x Hx. change (s_meta s2 x) with (UbMhDeq.d_meta s1 g x). unfold UbMhDeq.d_meta, UbMhDeq.d_next, UbMhDeq.d_prev. rewrite Hmulti. cbn [andb].
            destruct (Z.eqb_spec x g) as [->|NEx]; [exfalso; exact (proj1 (proj2 (wG_limbo s1 L (WF_groups s1 L W1) g ltac:(rewrite EL; exact Hx))) Hg)|].
            apply mr_set_links_id.
          - intros x Ux. exact Ux.
          - exact G'.
          - intros a Ha NEa. destruct (W' a Ha NEa) as [A|A]; [apply (meta_WOK L sp d s1 g a W1 Ug); lia | apply (active_WOK L sp d sc a Hsc A)].
          - kept_rw K'; reflexivity.
          - kept_rw K'; reflexivity.
          - kept_rw K'; reflexivity.
          - kept_rw K'; reflexivity.
          - kept_rw K'; reflexivity.
          - kept_rw K'; reflexivity.
          - eapply keeps_big; [exact KB | exact K' | reflexivity]. }
        apply (LG s2 M' mdl1 r' P2).
        * intros x k o Hx Hk E. rewrite SL2 in E. exact (NJ1 x k o Hx Hk E).
        * exact EL.
        * rewrite AL2. unfold UbMhDeq.l'. rewrite Hgsc, Hl. apply zremove_head. intros [].
        * kept_rw K'. exact A18.
      + (* [comment removed for export] *)
        destruct (NE ltac:(discriminate)) as [Enx NEg].
        assert (Hmulti : UbMhDeq.multi s1 g = true) by (apply (proj2 (UbMhDeq.multi_nxt s1 L g W1 Hinl)); exact NEg).
        destruct (UbMhDeq.nxt_facts s1 L g W1 Hmulti) as (Gnx & Snx & Unx & _ & NEnx & INnx).
        destruct (UbMhDeq.prv_facts s1 L g W1 Hmulti) as (Gpv & Spv & Upv & _ & NEpv & INpv).
        destruct (metaU_rng s1 L W1 _ Unx) as (X1 & X2 & _). destruct (metaU_rng s1 L W1 _ Upv) as (Y1 & Y2 & _).
        pose proof (metaU_sep s1 L W1 _ _ Upv Ug NEpv) as SEPp. pose proof (metaU_sep s1 L W1 _ _ Unx Ug NEnx) as SEPn.
        pose proof (rc_active s1 Mc (rp_ctx s1 Mc RP1) sc Hsc) as Ract. rewrite (wc_active s1 (WF_ctx s1 L W1) sc Hsc), Hl in Ract. cbn [head_of] in Ract.
        pose proof (meta_store_ok s1 L Mc W1 RP1 _ Upv) as SOKp. pose proof (meta_store_ok s1 L Mc W1 RP1 _ Unx) as SOKn.
        destruct (aDeqN Mc sc g (mr_next (s_meta s1 g)) (mr_prev (s_meta s1 g)) Hsc ltac:(unfold HEAPLO in *; lia) ltac:(unfold HEAPLO in *; lia) ltac:(unfold HEAPLO in *; lia)
                    Rfr Rnx Rpv Ract SOKa SOK16 ltac:(ceil; unfold HEAPLO in *; sok 40%nat SOKp) ltac:(ceil; unfold HEAPLO in *; sok 40%nat SOKn)
                    r rom A12 Q21 NEg SEPp SEPn) as (r' & RUN & E10 & K').
        eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
        set (M' := m_deqN Mc sc g (mr_next (s_meta s1 g)) (mr_prev (s_meta s1 g))) in *.
        assert (G' : mem_grows Mc M') by (unfold M', m_deqN; do 5 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
        assert (W' : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) ->
                     (g <= a < g + 16) \/ (mr_prev (s_meta s1 g) + 8 <= a < mr_prev (s_meta s1 g) + 16) \/ (mr_next (s_meta s1 g) <= a < mr_next (s_meta s1 g) + 8) \/
                     (ctx_active sc <= a < ctx_active sc + 8)).
        { intros a Ha NEa. ceil; unfold M', m_deqN, ctx_active, CTX, HEAPLO in *. wdiff2 NEa Mc a. }
        assert (NIg : ~ In g (nx0 :: rest')).
        { pose proof (wl_anodup s1 (WF_lists s1 L W1) sc) as ND. rewrite Hl in ND. apply NoDup_ListNoDup in ND. inversion ND. assumption. }
        assert (Ehd : head_of (UbMhDeq.l' s1 g) = mr_next (s_meta s1 g)).
        { unfold UbMhDeq.l'. rewrite Hgsc, Hl, (zremove_head g _ NIg). cbn [head_of]. symmetry. exact Enx. }
        assert (SEPpn : mr_prev (s_meta s1 g) = mr_next (s_meta s1 g) \/ mr_prev (s_meta s1 g) + 40 <= mr_next (s_meta s1 g) \/ mr_next (s_meta s1 g) + 40 <= mr_prev (s_meta s1 g)).
        { destruct (Z.eq_dec (mr_prev (s_meta s1 g)) (mr_next (s_meta s1 g))) as [E|NEpn]; [left; exact E | right; exact (metaU_sep s1 L W1 _ _ Upv Unx NEpn)]. }
        assert (Cprv : cell M' (mr_prev (s_meta s1 g) + 8) 8 (mr_next (s_meta s1 g))).
        { ceil; unfold M', m_deqN, HEAPLO, ctx_active, CTX in *. peel. peel. peel.
          apply cell_peel; [ | destruct SEPpn as [EE|SS]; [rewrite EE|]; wd_lenlit; rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | wd_lenlit; rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
          hit. }
        destruct (deq_close s1 L Mc M' g (spc sp d) W1 RP1 Hg Hav0 FR0 (spc_ok sp d Hsp)
                    ltac:(intros a Ha NEa; unfold UbMhDeq.d_wr; destruct (W' a Ha NEa) as [A|[A|[A|A]]];
                          [right; left; split; [exact Hinl | exact A] | right; right; left; split; [exact Hmulti | left; exact A]
                          | right; right; left; split; [exact Hmulti | right; exact A] | right; right; right; split; [exact Hinl | rewrite Hgsc; exact A]])
                    G' ltac:(ceil; unfold M', m_deqN, HEAPLO, ctx_active, CTX in *; cellw) ltac:(ceil; unfold M', m_deqN, HEAPLO, ctx_active, CTX in *; cellw)
                    ltac:(intros _; exact Cprv) ltac:(intros _; ceil; unfold M', m_deqN, HEAPLO, ctx_active, CTX in *; cellw)
                    ltac:(intros _; rewrite Hgsc, Ehd; ceil; unfold M', m_deqN, HEAPLO, ctx_active, CTX in *; cellw)) as [W2 RP2].
        pose proof (deq_facts s1 g) as (AL2 & ALo & _ & SL2 & GR2 & AI2 & MT2). rewrite Hgsc in AL2, ALo.
        set (s2 := UbMhDeq.st' s1 g) in *.
        assert (P2 : PT s2 M' mdl1 r').
        { apply (pt_step st L M mdl regs sp sc req d Hsc Hreq Hsp s1 Mc mdl1 r s2 M' r' P W2 RP2 eq_refl eq_refl eq_refl eq_refl).
          - intros k Hk. apply ALo. lia.
          - intros x Hx. change (s_meta s2 x) with (UbMhDeq.d_meta s1 g x). unfold UbMhDeq.d_meta, UbMhDeq.d_next, UbMhDeq.d_prev. rewrite Hmulti. cbn [andb].
            pose proof (wG_limbo s1 L (WF_groups s1 L W1) x ltac:(rewrite EL; exact Hx)) as (_ & NGx & _ & _).
            destruct (Z.eqb_spec x g) as [->|NEx]; [exfalso; exact (NGx Hg)|].
            destruct (Z.eqb_spec x (mr_prev (s_meta s1 g))) as [->|NEp]; [exfalso; exact (NGx Gpv)|].
            destruct (Z.eqb_spec x (mr_next (s_meta s1 g))) as [->|NEn]; [exfalso; exact (NGx Gnx)|].
            apply mr_set_links_id.
          - intros x Ux. exact Ux.
          - exact G'.
          - intros a Ha NEa. destruct (W' a Ha NEa) as [A|[A|[A|A]]];
              [apply (meta_WOK L sp d s1 g a W1 Ug); lia | apply (meta_WOK L sp d s1 _ a W1 Upv); lia | apply (meta_WOK L sp d s1 _ a W1 Unx); lia | apply (active_WOK L sp d sc a Hsc A)].
          - kept_rw K'; reflexivity.
          - kept_rw K'; reflexivity.
          - kept_rw K'; reflexivity.
          - kept_rw K'; reflexivity.
          - kept_rw K'; reflexivity.
          - kept_rw K'; reflexivity.
          - eapply keeps_big; [exact KB | exact K' | reflexivity]. }
        assert (AL2' : s_alist s2 sc = mr_next (s_meta s1 g) :: rest').
        { rewrite AL2. unfold UbMhDeq.l'. rewrite Hgsc, Hl, (zremove_head g _ NIg). rewrite Enx. reflexivity. }
        pose proof (wl_rest s1 (WF_lists s1 L W1) sc (mr_next (s_meta s1 g)) ltac:(rewrite Hl; exact IN) ltac:(rewrite Hl; cbn; intros E; exact (NEg E))) as [AVn FRn].
        apply (LA5 s2 M' mdl1 r' (mr_next (s_meta s1 g)) rest' P2).
        * intros x k o Hx Hk E. rewrite SL2 in E. exact (NJ1 x k o Hx Hk E).
        * exact EL.
        * exact AL2'.
        * rewrite (proj1 (MT2 _)). exact AVn.
        * rewrite (proj1 (proj2 (MT2 _))). exact FRn.
        * exact E10.
    - (* [comment removed for export] *)
      destruct (aRot Mc sc g (mr_freed (s_meta s1 g)) (mr_next (s_meta s1 g)) Hsc ltac:(unfold HEAPLO in *; lia) FRR Rfr Rnx SOKa r rom A12 Q21 FRNZ)
        as (r' & RUN & E10 & E11 & K').
      eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
      destruct (rot_close st L M mdl regs sp sc req d Hsc Hreq Hsp s1 Mc mdl1 r g rest r' _ P Hl Hav0 FRNZ
                  ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity)
                  ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity) ltac:(kept_rw K'; reflexivity) K' eq_refl)
        as (P2 & AL2 & SL2 & MT2 & GR2' & AI2 & LB2 & KD2 & HD2 & _ & _ & _ & AV2 & FR2 & _ & _).
      set (s2 := UbMhRotate.st' s1 sc g rest) in *. set (nx := mr_next (s_meta s1 g)) in *.
      destruct (rest ++ [g]) as [|h2 rest2] eqn:EL2; [destruct rest; discriminate EL2|]. cbn in HD2. subst h2.
      apply (LA5 s2 _ mdl1 r' nx rest2 P2).
      + intros x k o Hx Hk E. rewrite SL2 in E. exact (NJ1 x k o Hx Hk E).
      + rewrite LB2. exact EL.
      + exact AL2.
      + rewrite MT2. exact AV2.
      + rewrite MT2. exact FR2.
      + exact E10.
  Qed.

  (* [comment removed for export] *)
  Lemma L_A2 : forall s1 Mc mdl1 r g,
    PT s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st -> head_of (s_alist s1 sc) = g -> g <> 0 ->
    getr r 12 = Z_to_bv 64 g -> getr r 18 = Z_to_bv 64 req ->
    kat RSEGS (mkCfg (mkst r (0x67314%bv : word) Mc rom) mdl1) Q.
  Proof.
    intros s1 Mc mdl1 r g P NJ1 EL Hhd NZ A12 A18.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    destruct (head_facts L sc s1 g W1 Hhd NZ) as (rest & Hl & Hg & Hgsc).
    pose proof (wG_each s1 L (WF_groups s1 L W1) g Hg) as WG. pose proof (wg_avr s1 L g WG) as AVR.
    destruct (G_meta_cells s1 L Mc W1 RP1 g Hg) as (ar1 & k1 & _ & _ & _ & _ & Glo & Ghi & _ & RM1 & _ & _).
    pose proof (rm_avail Mc g _ RM1) as Rav.
    destruct (Z.eq_dec (mr_avail (s_meta s1 g)) 0) as [AV0|AVNZ].
    - destruct (aAvail0 Mc g (mr_avail (s_meta s1 g)) ltac:(unfold HEAPLO in *; lia) AVR Rav r rom A12 AV0) as (r' & RUN & E11 & K').
      eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
      apply (L_A3 s1 Mc mdl1 r' g rest); try assumption.
      + apply (pt_regs st L M mdl regs sp sc d s1 Mc mdl1 r r' P); try (kept_rw K'; reflexivity). eapply keeps_big; [exact KB | exact K' | reflexivity].
      + kept_rw K'. exact A12.
      + kept_rw K'. exact A18.
    - destruct (aAvailT Mc g (mr_avail (s_meta s1 g)) ltac:(unfold HEAPLO in *; lia) AVR Rav r rom A12 AVNZ) as (r' & RUN & E10 & E11 & K').
      eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
      apply (LT s1 Mc mdl1 r' g (mr_avail (s_meta s1 g))); try assumption; try reflexivity.
      apply (pt_regs st L M mdl regs sp sc d s1 Mc mdl1 r r' P); try (kept_rw K'; reflexivity). eapply keeps_big; [exact KB | exact K' | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma L_A1 : forall r1,
    getr r1 2 = Z_to_bv 64 (sp - 144) -> getr r1 8 = Z_to_bv 64 sc -> getr r1 18 = Z_to_bv 64 req ->
    getr r1 20 = Z_to_bv 64 A_CANARY -> getr r1 22 = Z_to_bv 64 MLOCK -> getr r1 23 = Z_to_bv 64 (MLOCK + 8 * sc) ->
    keeps_but BIG regs r1 ->
    kat RSEGS (mkCfg (mkst r1 (0x67308%bv : word) (M1 st M regs sp) rom) mdl) Q.
  Proof.
    intros r1 E2 E8 E18 E20 E22 E23 K1.
    pose proof (M1_REP st L M regs sp d HWF HREP Hsp) as RP1.
    set (hd := head_of (s_alist st sc)).
    pose proof (rc_active st (M1 st M regs sp) (rp_ctx st _ RP1) sc Hsc) as Ract. rewrite (wc_active st (WF_ctx st L HWF) sc Hsc) in Ract. fold hd in Ract.
    assert (HDR : 0 <= hd < 2 ^ 64).
    { subst hd. destruct (s_alist st sc) as [|h t] eqn:El; cbn; [lia|].
      destruct (member_facts L sc st h HWF ltac:(rewrite El; left; reflexivity)) as (_ & _ & _ & A & B). ceil; unfold HEAPLO in *. lia. }
    destruct (Z.eq_dec hd 0) as [HZ|HNZ].
    - destruct (aHead0 (M1 st M regs sp) sc hd Hsc HDR Ract r1 rom E23 HZ) as (r2 & RUN & F21 & F12 & K2).
      eapply kat_msteps; [exact Hh | exact Hlz | exact RUN |].
      assert (P1 : PT st (M1 st M regs sp) mdl r2).
      { apply (pt_first st L M mdl regs sp sc d HWF HREP HLG Hh Hlz Hmat Hsp DEF); try (kept_rw K2; assumption).
        eapply keeps_big; [exact K1 | exact K2 | reflexivity]. }
      apply (LG st (M1 st M regs sp) mdl r2 P1 NJ eq_refl).
      + subst hd. destruct (s_alist st sc) as [|h t] eqn:El; [reflexivity|]. exfalso. cbn in HZ.
        destruct (member_facts L sc st h HWF ltac:(rewrite El; left; reflexivity)) as (_ & _ & _ & A & B). unfold HEAPLO in *. lia.
      + kept_rw K2. exact E18.
    - destruct (aHead1 (M1 st M regs sp) sc hd Hsc HDR Ract r1 rom E23 HNZ) as (r2 & RUN & F21 & F12 & K2).
      eapply kat_msteps; [exact Hh | exact Hlz | exact RUN |].
      assert (P1 : PT st (M1 st M regs sp) mdl r2).
      { apply (pt_first st L M mdl regs sp sc d HWF HREP HLG Hh Hlz Hmat Hsp DEF); try (kept_rw K2; assumption).
        eapply keeps_big; [exact K1 | exact K2 | reflexivity]. }
      apply (L_A2 st (M1 st M regs sp) mdl r2 hd P1 NJ eq_refl eq_refl HNZ F12). kept_rw K2. exact E18.
  Qed.

  Lemma as_body : kat RSEGS (mkCfg (mkst regs (0x672b0%bv : word) M rom) mdl) Q.
  Proof.
    apply (as_head st M mdl regs rom sp sc req Q d HREP Hh Hlz Hsc R10 R11 R2 Hsp DEF).
    intros r1 E2 E8 E18 E20 E22 E23 K1 _. exact (L_A1 r1 E2 E8 E18 E20 E22 E23 K1).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_A1_agf : agf st -> forall r1,
    getr r1 2 = Z_to_bv 64 (sp - 144) -> getr r1 8 = Z_to_bv 64 sc -> getr r1 18 = Z_to_bv 64 req ->
    getr r1 20 = Z_to_bv 64 A_CANARY -> getr r1 22 = Z_to_bv 64 MLOCK -> getr r1 23 = Z_to_bv 64 (MLOCK + 8 * sc) ->
    keeps_but BIG regs r1 ->
    kat RSEGS (mkCfg (mkst r1 (0x67308%bv : word) (M1 st M regs sp) rom) mdl) Q.
  Proof.
    intros AGF r1 E2 E8 E18 E20 E22 E23 K1.
    pose proof (M1_REP st L M regs sp d HWF HREP Hsp) as RP1.
    set (hd := head_of (s_alist st sc)).
    pose proof (rc_active st (M1 st M regs sp) (rp_ctx st _ RP1) sc Hsc) as Ract. rewrite (wc_active st (WF_ctx st L HWF) sc Hsc) in Ract. fold hd in Ract.
    assert (HDR : 0 <= hd < 2 ^ 64).
    { subst hd. destruct (s_alist st sc) as [|h t] eqn:El; cbn; [lia|].
      destruct (member_facts L sc st h HWF ltac:(rewrite El; left; reflexivity)) as (_ & _ & _ & A & B). ceil; unfold HEAPLO in *. lia. }
    destruct (Z.eq_dec hd 0) as [HZ|HNZ].
    - destruct (aHead0 (M1 st M regs sp) sc hd Hsc HDR Ract r1 rom E23 HZ) as (r2 & RUN & F21 & F12 & K2).
      eapply kat_msteps; [exact Hh | exact Hlz | exact RUN |].
      assert (P1 : PT st (M1 st M regs sp) mdl r2).
      { apply (pt_first st L M mdl regs sp sc d HWF HREP HLG Hh Hlz Hmat Hsp DEF); try (kept_rw K2; assumption).
        eapply keeps_big; [exact K1 | exact K2 | reflexivity]. }
      apply (LGa st (M1 st M regs sp) mdl r2 P1 NJ eq_refl).
      + subst hd. destruct (s_alist st sc) as [|h t] eqn:El; [reflexivity|]. exfalso. cbn in HZ.
        destruct (member_facts L sc st h HWF ltac:(rewrite El; left; reflexivity)) as (_ & _ & _ & A & B). unfold HEAPLO in *. lia.
      + kept_rw K2. exact E18.
      + exact AGF.
    - destruct (aHead1 (M1 st M regs sp) sc hd Hsc HDR Ract r1 rom E23 HNZ) as (r2 & RUN & F21 & F12 & K2).
      eapply kat_msteps; [exact Hh | exact Hlz | exact RUN |].
      assert (P1 : PT st (M1 st M regs sp) mdl r2).
      { apply (pt_first st L M mdl regs sp sc d HWF HREP HLG Hh Hlz Hmat Hsp DEF); try (kept_rw K2; assumption).
        eapply keeps_big; [exact K1 | exact K2 | reflexivity]. }
      assert (A18 : getr r2 18 = Z_to_bv 64 req) by (kept_rw K2; exact E18).
      assert (Ehd : head_of (s_alist st sc) = hd) by reflexivity.
      clearbody hd. revert P1 F12 A18. generalize (M1 st M regs sp) as Mc. generalize r2 as r. clear r2 RUN F21 K2 Ract RP1. clear E2 E8 E18 E20 E22 E23 K1 r1. intros r Mc P A12 A18.
      (* [comment removed for export] *)
      pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
      destruct (head_facts L sc st hd W1 Ehd HNZ) as (rest & Hl & Hg & Hgsc).
      pose proof (wG_each st L (WF_groups st L W1) hd Hg) as WG. pose proof (wg_avr st L hd WG) as AVR. pose proof (wg_frr st L hd WG) as FRR.
      destruct (G_meta_cells st L Mc W1 RP1 hd Hg) as (ar1 & k1 & _ & _ & _ & _ & Glo & Ghi & G8 & RM1 & _ & _).
      pose proof (rm_avail Mc hd _ RM1) as Rav.
      destruct (AGF hd Hg) as [AV0 FR0].
      destruct (aAvail0 Mc hd (mr_avail (s_meta st hd)) ltac:(unfold HEAPLO in *; lia) AVR Rav r rom A12 AV0) as (r' & RUN' & E11 & K').
      eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN' |].
      assert (P' : PT st Mc mdl r').
      { apply (pt_regs st L M mdl regs sp sc d st Mc mdl r r' P); try (kept_rw K'; reflexivity). eapply keeps_big; [exact KB | exact K' | reflexivity]. }
      assert (A12' : getr r' 12 = Z_to_bv 64 hd) by (kept_rw K'; exact A12).
      assert (A18' : getr r' 18 = Z_to_bv 64 req) by (kept_rw K'; exact A18).
      clear P Q2 Q8 Q20 Q21 Q22 Q23 KB RUN' E11. revert P' A12' A18'. generalize r' as r0. clear r r' K' A12 A18. intros r P A12 A18.
      pose proof P as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Q2 Q8 Q20 Q21 Q22 Q23 KB].
      (* [comment removed for export] *)
      destruct (member_facts L sc st hd W1 ltac:(rewrite Hl; left; reflexivity)) as (_ & _ & Ug & _ & _).
      destruct RM1 as [Rpv Rnx Rme Rav2 Rfr RW]. rewrite FR0 in Rfr.
      pose proof (ctx_store_ok st Mc RP1) as SOKc.
      assert (SOKa : store_ok RSEGS Mc (Z_to_bv 64 (ctx_active sc)) 8%nat = true) by (unfold ctx_active, CTX in *; sok 928%nat SOKc).
      destruct (next_of_head L sp sc req d Hsc Hreq Hsp st hd rest W1 Hl) as (SELF & IN & NE).
      pose proof (meta_store_ok st L Mc W1 RP1 hd Ug) as SOKg.
      assert (SOK16 : store_ok RSEGS Mc (Z_to_bv 64 hd) 16%nat = true) by (ceil; unfold HEAPLO in *; sok 40%nat SOKg).
      assert (Hinl : UbMhDeq.inl st hd = true) by (apply (proj2 (UbMhDeq.inl_true st hd)); rewrite Hgsc, Hl; left; reflexivity).
      assert (Hrest : rest = []).
      { destruct rest as [|nx0 rest']; [reflexivity|]. exfalso.
        assert (Inx : In nx0 (s_alist st sc)) by (rewrite Hl; right; left; reflexivity).
        pose proof (wl_anodup st (WF_lists st L W1) sc) as ND. rewrite Hl in ND.
        assert (NEx : nx0 <> head_of (s_alist st sc)).
        { rewrite Hl. cbn. intros E. subst nx0. inversion ND as [|x l NI ND']. apply NI. left. }
        destruct (wl_rest st (WF_lists st L W1) sc nx0 Inx NEx) as [_ FRnz].
        destruct (wl_aU st (WF_lists st L W1) sc nx0 Inx) as (_ & Gnx & _).
        exact (FRnz (proj2 (AGF nx0 Gnx))). }
      subst rest.
      assert (Enx : mr_next (s_meta st hd) = hd) by (apply (proj2 SELF); reflexivity).
      destruct (aDeqS Mc sc hd (mr_next (s_meta st hd)) Hsc ltac:(unfold HEAPLO in *; lia) ltac:(rewrite Enx; unfold HEAPLO in *; lia) Rfr Rnx SOKa SOK16
                  r rom A12 Q21 Enx) as (r' & RUN & E10 & K').
      eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
      set (M' := m_deqS Mc sc hd) in *.
      assert (G' : mem_grows Mc M') by (unfold M', m_deqS; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (W' : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) -> (hd <= a < hd + 16) \/ (ctx_active sc <= a < ctx_active sc + 8)).
      { intros a Ha NEa. ceil; unfold M', m_deqS, ctx_active, CTX, HEAPLO in *. wdiff2 NEa Mc a. }
      assert (Hmulti : UbMhDeq.multi st hd = false).
      { destruct (UbMhDeq.multi st hd) eqn:E; [|reflexivity]. exfalso. apply (proj1 (UbMhDeq.multi_nxt st L hd W1 Hinl) E). exact Enx. }
      destruct (deq_close st L Mc M' hd (spc sp d) W1 RP1 Hg AV0 FR0 (spc_ok sp d Hsp)
                  ltac:(intros a Ha NEa; unfold UbMhDeq.d_wr; destruct (W' a Ha NEa) as [A|A]; [right; left; split; [exact Hinl | exact A] | right; right; right; split; [exact Hinl | rewrite Hgsc; exact A]])
                  G' ltac:(ceil; unfold M', m_deqS, HEAPLO, ctx_active, CTX in *; cellw) ltac:(ceil; unfold M', m_deqS, HEAPLO, ctx_active, CTX in *; cellw)
                  ltac:(rewrite Hmulti; intros X; discriminate X) ltac:(rewrite Hmulti; intros X; discriminate X)
                  ltac:(intros _; rewrite Hgsc; unfold UbMhDeq.l'; rewrite Hgsc, Hl, (zremove_head hd [] ltac:(intros [])); cbn [head_of];
                        ceil; unfold M', m_deqS, HEAPLO, ctx_active, CTX in *; cellw)) as [W2 RP2].
      pose proof (deq_facts st hd) as (AL2 & ALo & _ & SL2 & GR2 & AI2 & MT2). rewrite Hgsc in AL2, ALo.
      set (s2 := UbMhDeq.st' st hd) in *.
      assert (P2 : PT s2 M' mdl r').
      { apply (pt_step st L M mdl regs sp sc req d Hsc Hreq Hsp st Mc mdl r s2 M' r' P W2 RP2 eq_refl eq_refl eq_refl eq_refl).
        - intros k Hk. apply ALo. lia.
        - intros x Hx. change (s_meta s2 x) with (UbMhDeq.d_meta st hd x). unfold UbMhDeq.d_meta, UbMhDeq.d_next, UbMhDeq.d_prev. rewrite Hmulti. cbn [andb].
          destruct (Z.eqb_spec x hd) as [->|NEx]; [exfalso; exact (proj1 (proj2 (wG_limbo st L (WF_groups st L W1) hd Hx)) Hg)|].
          apply mr_set_links_id.
        - intros x Ux. exact Ux.
        - exact G'.
        - intros a Ha NEa. destruct (W' a Ha NEa) as [A|A]; [apply (meta_WOK L sp d st hd a W1 Ug); lia | apply (active_WOK L sp d sc a Hsc A)].
        - kept_rw K'; reflexivity.
        - kept_rw K'; reflexivity.
        - kept_rw K'; reflexivity.
        - kept_rw K'; reflexivity.
        - kept_rw K'; reflexivity.
        - kept_rw K'; reflexivity.
        - eapply keeps_big; [exact KB | exact K' | reflexivity]. }
      apply (LGa s2 M' mdl r' P2).
      + intros x k o Hx Hk E. rewrite SL2 in E. exact (NJ x k o Hx Hk E).
      + reflexivity.
      + rewrite AL2. unfold UbMhDeq.l'. rewrite Hgsc, Hl. apply zremove_head. intros [].
      + kept_rw K'. exact A18.
      + intros x Hx. assert (Hx1 : is_group st x) by (unfold is_group in Hx |- *; rewrite <- GR2; exact Hx).
        destruct (MT2 x) as (Eav & Efr & _). destruct (AGF x Hx1) as [A0 F0].
        split; [etransitivity; [exact Eav | exact A0] | etransitivity; [exact Efr | exact F0]].
  Qed.

  Lemma as_body_agf : agf st -> kat RSEGS (mkCfg (mkst regs (0x672b0%bv : word) M rom) mdl) Q.
  Proof.
    intros AGF. apply (as_head st M mdl regs rom sp sc req Q d HREP Hh Hlz Hsc R10 R11 R2 Hsp DEF).
    intros r1 E2 E8 E18 E20 E22 E23 K1 _. exact (L_A1_agf AGF r1 E2 E8 E18 E20 E22 E23 K1).
  Qed.
End ASF.
End UbMhASlotKB.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotW5 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhASlotKG.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount.UbMhCountSpec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.UbMhASpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotW5.UbMhASlotW4 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotW5 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF.UbMhASlotT1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ASG.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M : mem) (mdl : Model)
            (regs : bvmap 5 word) (rom : word -> option byte) (sp sc req : Z) (d : nat)
            (F : kfam) (bi bo : bool).
  Hypothesis HL : kfam_laws RSEGS F.
  Hypothesis HAM : AM_SPEC3.
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HLG : LEDGER st (m_vmmaps mdl).
  Hypothesis NJ : nojunk st.
  Hypothesis Hh : m_halted mdl = None.
  Hypothesis Hlz : m_vm_lazy mdl = [].
  Hypothesis Hmat : m_vm_materialized mdl = [].
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hd : dle (dbound (16 * size_class sc)) d.
  Hypothesis Hlimbo : zlen (s_limbo st) + Z.of_nat d + 1 <= 8.
  Hypothesis Hreq : 0 <= req /\ req + 4 <= 16 * size_class sc.
  Hypothesis HBUD : PHI L + MBASE <= vm_limit (m_vmmaps mdl).
  Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 req.
  Hypothesis R2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis Rra : ret_ok (getr regs 1).
  Hypothesis R4 : getr regs 4 = Z_to_bv 64 TPV.
  Hypothesis Hsp : CEIL + ASSTK d <= sp /\ sp < 2 ^ 64.
  Hypothesis DEF : defined M (sp - ASSTK d) sp.
  Hypothesis HQ : forall c', as_ok st L sc req d sp regs M mdl rom c' -> kfx F bi c'.
  Hypothesis HQF : forall c', as_fail st L sc d sp regs M mdl rom c' -> Kf F c'.
  Hypothesis IHd : forall d', (d' < d)%nat -> AS_SPEC3 d'.

  #[local] Notation PT := (pt st L M mdl regs sp sc d).
  #[local] Notation GBR := (gbr st L M mdl regs sp sc req d).
  #[local] Notation WOKa := (WOK L sp d).

  (* [comment removed for export] *)
  Hypothesis HL_N : forall s2 M2 mdl2 r m cnt, GBR s2 M2 mdl2 r m cnt -> 16 * size_class sc * cnt + 16 <= 2048 ->
    (bo = true -> bi = true \/ agf s2) ->
    kat RSEGS (mkCfg (mkst r (0x675c0%bv : word) M2 rom) mdl2) (kfx F bo).
  Hypothesis HL_M : forall s2 M2 mdl2 r m cnt, GBR s2 M2 mdl2 r m cnt -> 2048 < 16 * size_class sc * cnt + 16 ->
    kat RSEGS (mkCfg (mkst r (0x6757c%bv : word) M2 rom) mdl2) (kfx F bo).

  Lemma scl_rng : 1 <= size_class sc <= 8191. Proof. pose proof (size_class_pos sc Hsc). lia. Qed.
  Lemma stk272 : 288 <= ASSTK d. Proof. apply ASSTK_ge. Qed.

  (* [comment removed for export] *)
  Definition gcnt (s2 : mst) : Z := g4cnt (16 * size_class sc) (gsel sc (size_class sc) (c_usage (s_ctx s2) sc)).

  (* [comment removed for export] *)
  Lemma L_G_cont : forall s2 M2 mdl2 r2 m,
    PT s2 M2 mdl2 r2 -> nojunk s2 ->
    s_limbo s2 = m :: s_limbo st -> s_alist s2 sc = [] -> metaU s2 m -> s_meta s2 m = meta_zero -> ~ In m (s_limbo st) ->
    (bo = true -> bi = true \/ agf s2) ->
    getr r2 10 = Z_to_bv 64 m -> getr r2 18 = Z_to_bv 64 req -> getr r2 19 = Z_to_bv 64 (2 * sc) ->
    getr r2 24 = Z_to_bv 64 (size_class sc) -> getr r2 25 = Z_to_bv 64 A_TAB_SC ->
    (forall r, GBR s2 M2 mdl2 r m (gcnt s2) -> 16 * size_class sc * gcnt s2 + 16 <= 2048 ->
       (bo = true -> bi = true \/ agf s2) ->
       kat RSEGS (mkCfg (mkst r (0x675c0%bv : word) M2 rom) mdl2) (kfx F bo)) ->
    (forall r, GBR s2 M2 mdl2 r m (gcnt s2) -> 2048 < 16 * size_class sc * gcnt s2 + 16 ->
       kat RSEGS (mkCfg (mkst r (0x6757c%bv : word) M2 rom) mdl2) (kfx F bo)) ->
    kat RSEGS (mkCfg (mkst r2 (0x674a8%bv : word) M2 rom) mdl2) (kfx F bo).
  Proof.
    intros s2 M2 mdl2 r2 m P2 NJ2 Elim Hnil Um Zm NLm2 SIDE2 F10 E18 E19 E24 E25 HN2 HM2.
    pose proof P2 as [W2 RP2 LG2 Hh2 Hlz2 Hmat2 Hfs2 Hfds2 Hlim2 Hcan2 Herr2 BL2 LM2 MU2 FR2 DF2 SK2 Q2 Q8 Q20 Q21 Q22 Q23 KB2].
    pose proof scl_rng as SCL. pose proof stk272 as S272. pose proof Hsp as [SP1 SP2].
    destruct (metaU_rng s2 L W2 m Um) as (MR1 & MR2 & MR8).
    (* [comment removed for export] *)
    pose proof (rc_usage s2 M2 (rp_ctx s2 M2 RP2) sc Hsc) as Ru. pose proof (wc_usage s2 (WF_ctx s2 L W2) sc) as UR.
    pose proof (rc_pagesize s2 M2 (rp_statics s2 M2 RP2)) as Rpg.
    destruct (aGrp0 M2 sc m (c_usage (s_ctx s2) sc) (size_class sc) Hsc ltac:(unfold HEAPLO in *; lia) ltac:(lia) Ru Rpg r2 rom F10 Q23 E24)
      as (r3 & RUN3 & G9 & G10 & G11 & G12 & G24 & K3).
    eapply kat_msteps; [exact Hh2 | exact Hlz2 | exact RUN3 |].
    (* [comment removed for export] *)
    destruct (aGsel M2 sc (size_class sc) (c_usage (s_ctx s2) sc) Hsc eq_refl UR (rc_tab_sc s2 M2 (rp_statics s2 M2 RP2)) r3 rom
                G10 G12 ltac:(kept_rw K3; exact Q8) ltac:(kept_rw K3; exact E19) G24 ltac:(kept_rw K3; exact E25)) as (r4 & RUN4 & J19 & K4).
    eapply kat_msteps; [exact Hh2 | exact Hlz2 | exact RUN4 |].
    destruct (gsel_facts sc (size_class sc) (c_usage (s_ctx s2) sc) Hsc eq_refl) as (GS1 & GS2 & GS3).
    set (g0 := gsel sc (size_class sc) (c_usage (s_ctx s2) sc)) in *.
    (* [comment removed for export] *)
    destruct (aG4 M2 (16 * size_class sc) g0 ltac:(lia) ltac:(lia) r4 rom J19 ltac:(kept_rw K4; exact G24) ltac:(kept_rw K4; kept_rw K3; exact G11))
      as (r5 & RUN5 & U19 & U14 & U15 & U12 & U13 & K5).
    eapply kat_msteps; [exact Hh2 | exact Hlz2 | exact RUN5 |].
    assert (Ecnt : g4cnt (16 * size_class sc) g0 = gcnt s2) by reflexivity.
    rewrite Ecnt in *.
    set (cnt := gcnt s2) in *.
    assert (CF : 1 <= cnt <= 32 /\ 16 * size_class sc * cnt < 2 ^ 20 /\ (sc = 7 -> cnt <= 31) /\ (cnt = 1 -> 2048 < 16 * size_class sc + 16)).
    { subst cnt. unfold gcnt. fold g0. unfold g4cnt. destruct (Z.eqb_spec g0 1) as [E1'|NE1].
      - destruct (Z.ltb_spec 2048 (16 * size_class sc + 16)); [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros; lia.
      - lia. }
    assert (GB : GBR s2 M2 mdl2 r5 m cnt).
    { split.
      { apply (pt_regs st L M mdl regs sp sc d s2 M2 mdl2 r2 r5 P2); try (kept_rw K5; kept_rw K4; kept_rw K3; reflexivity).
        eapply keeps_big; [eapply keeps_big; [eapply keeps_big; [exact KB2 | exact K3 | reflexivity] | exact K4 | reflexivity] | exact K5 | reflexivity]. }
      split; [exact NJ2|]. split; [exact Elim|]. split; [exact Hnil|].
      split; [exact Um|]. split; [exact Zm|]. split; [exact NLm2|].
      split; [kept_rw K5; kept_rw K4; exact G9|]. split; [kept_rw K5; kept_rw K4; exact G10|]. split; [kept_rw K5; kept_rw K4; exact G11|].
      split; [kept_rw K5; kept_rw K4; kept_rw K3; exact E18|].
      split; [exact U19|]. split; [kept_rw K5; kept_rw K4; exact G24|]. split; [kept_rw K5; kept_rw K4; kept_rw K3; exact E25|].
      split; [exact U14|]. split; [exact U12|]. exact CF. }
    destruct (Z.leb_spec (16 * size_class sc * cnt + 16) 2048) as [LE|GT].
    - apply (HN2 r5 GB LE SIDE2).
    - apply (HM2 r5 GB). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_G : forall s1 Mc mdl1 r,
    PT s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st -> s_alist s1 sc = [] -> getr r 18 = Z_to_bv 64 req ->
    (bo = true -> bi = true \/ agf s1) ->
    kat RSEGS (mkCfg (mkst r (0x67490%bv : word) Mc rom) mdl1) (kfx F bo).
  Proof.
    intros s1 Mc mdl1 r P NJ1 EL Hnil Q18 SIDE.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    pose proof scl_rng as SCL. pose proof stk272 as S272.
    (* [comment removed for export] *)
    destruct (aMeta Mc sc Hsc (sz_img_of_REP s1 Mc RP1) r rom Q8) as (r1 & RUN1 & E19 & E25 & E24 & E1 & K1).
    eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN1 |].
    destruct (budget L mdl d HBUD s1 mdl1 W1 NJ1 ltac:(rewrite EL; unfold zlen in *; lia) Hlim1) as (HCA & HCR & HRS).
    assert (E2 : getr r1 2 = Z_to_bv 64 (sp - 144)) by (kept_rw K1; exact Q2).
    apply (kat_of_kfx F bo). replace (0x66c68%bv : word) with (Z_to_bv 64 AM_ENTRY) by (apply bv_eq; reflexivity).
    apply (HAM F bo bo s1 L [] Mc mdl1 r1 rom (sp - 144) HL (fun E => E) W1 RP1 (proj1 (LEDGERX_nil s1 _) LG1) xok_nil Hh1 Hlz1 Hmat1 HCA).
    { cbn [length Z.of_nat]. lia. }
    { rewrite XSUM_nil. lia. }
    { exact E2. }
    { rewrite E1. apply ret_ok_even. reflexivity. }
    { unfold AMSTK. ceil. lia. }
    { lia. }
    { kept_rw K1. kept_rw KB. exact R4. }
    { intros y Hy. apply DF1. unfold AMSTK in Hy. lia. }
    2: { (* [comment removed for export] *)
      intros c' PF.
      destruct PF as (s2 & M2 & mdl2 & r2 & -> & W2 & RP2 & LG2 & Hh2 & Hlz2 & Hmat2 & Hfs2 & Hfds2 & Hvl2 &
                      Elim & Efl & Ear & Emeta & Eerr & KEEP & REG & F10 & F2 & K2 & M2W & DEF2).
      destruct KEEP as (Egrp & Eslot & Ealist & Eai & Ekind & Ecan & Eact & Eus & Ebn & Euq & Esq & Ectr & Esec & Emg & Elm2 & MU2).
      rewrite E1. replace (Z_to_bv 64 423080) with (0x674a8%bv : word) by (apply bv_eq; reflexivity).
      apply (kf_of_kat F HL).
      apply (L_G1 st L M mdl regs rom sp sc (Kf F) d R2 Rra Hsp HQF s2 M2 mdl2 r2).
      - constructor; try assumption.
        + apply (proj2 (LEDGERX_nil s2 _)). exact LG2.
        + rewrite Hfs2. exact Hfs1.
        + rewrite Hfds2. exact Hfds1.
        + rewrite Hvl2. exact Hlim1.
        + rewrite Ecan. exact Hcan1.
        + intros x Hx. rewrite (Elm2 x ltac:(rewrite EL; exact Hx)). exact (LM1 x Hx).
        + intros x Ux. exact (MU2 x (MU1 x Ux)).
        + intros a Ha NE. destruct (decide (M2 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))) as [E|NE2].
          * apply FR1; [exact Ha | congruence].
          * destruct (M2W a Ha NE2) as [A|[A|[A|(rr & Hrr & NK & A)]]].
            -- left. unfold AMSTK in A. lia.
            -- right; right; left. exact A.
            -- right; right; right. exact A.
            -- right; left. exact (nongroup_nonapp L d s2 rr a W2 Hrr NK A).
        + intros a Ha. destruct (decide (M2 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))) as [E|NE]; [rewrite E; exact (DF1 a Ha)|].
          destruct (M2W a ltac:(ceil; lia) NE) as [A|[A|[A|(rr & Hrr & NK & A)]]].
          * apply DEF2. exact A.
          * exfalso. ceil; unfold CTX_END, CTX in *. lia.
          * exfalso. ceil; unfold A_ERRNO, TPV in *. lia.
          * exfalso. destruct (nongroup_nonapp L d s2 rr a W2 Hrr NK A) as [B _]. ceil. lia.
        + apply (stk_transfer st regs sp sc req d Hsc Hreq Hsp Mc M2); [|exact SK1]. intros y Hy.
          destruct (decide (M2 (Z_to_bv 64 y) = Mc (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
          destruct (M2W y ltac:(ceil; lia) NE) as [A|[A|[A|(rr & Hrr & NK & A)]]].
          * unfold AMSTK in A. lia.
          * ceil; unfold CTX_END, CTX in *. lia.
          * ceil; unfold A_ERRNO, TPV in *. lia.
          * destruct (nongroup_nonapp L d s2 rr y W2 Hrr NK A) as [B _]. ceil. lia.
        + rewrite F2. exact E2.
        + kept_rw K2. kept_rw K1. exact Q20.
        + eapply keeps_big; [eapply keeps_big; [exact KB | exact K1 | reflexivity] | exact K2 | reflexivity].
      - intros x k o Hx Hk E. rewrite Eslot in E. unfold is_group in Hx. rewrite Egrp in Hx.
        apply (NJ1 x k o Hx); [|exact E]. unfold g_lastidx, g_W in *. rewrite (Emg x Hx) in Hk. exact Hk.
      - rewrite Elim. exact EL.
      - exact F10. }
    (* [comment removed for export] *)
    intros c' POST. apply (kfx_of_kat F HL bo).
    destruct POST as (s2 & M2 & mdl2 & r2 & m & -> & W2 & RP2 & LG2 & Hh2 & Hlz2 & Hmat2 & Hfs2 & Hfds2 & Hvl2 &
                      Elim & Um & Zm & NLm2 & Efl & Eerr & KEEP & REG & F10 & F2 & K2 & M2W & DEF2).
    destruct KEEP as (Egrp & Eslot & Ealist & Eai & Ekind & Ecan & Eact & Eus & Ebn & Euq & Esq & Ectr & Esec & Emg & Elm2 & MU2).
    destruct REG as (RS2 & RL2 & RX2).
    rewrite E1. replace (Z_to_bv 64 423080) with (0x674a8%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (Eerr' : s_errno s2 = s_errno s1 \/ s_errno s2 = 12) by (first [exact Eerr | left; exact Eerr]).
    assert (P2 : PT s2 M2 mdl2 r2).
    { apply (pt_step2 st L M mdl regs sp sc req d Hsc Hreq Hsp s1 Mc mdl1 r s2 M2 mdl2 r2 P W2 RP2); try assumption.
      - apply (proj2 (LEDGERX_nil s2 _)). exact LG2.
      - intros k Hk. rewrite Ealist. reflexivity.
      - intros x Hx. apply Elm2. rewrite EL. exact Hx.
      - (* [comment removed for export] *)
        intros a Ha. destruct (decide (M2 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))) as [E|NE]; [rewrite E; exact (DF1 a Ha)|].
        destruct (M2W a ltac:(ceil; lia) NE) as [[A|[A|[A|(rr & Hrr & NK & A)]]]|HOLE].
        + apply DEF2. exact A.
        + exfalso. ceil; unfold CTX_END, CTX in *. lia.
        + exfalso. ceil; unfold A_ERRNO, TPV in *. lia.
        + exfalso. destruct (nongroup_nonapp L d s2 rr a W2 Hrr NK A) as [B _]. ceil. lia.
        + (* [comment removed for export] *)
          exfalso. destruct (am_holeR_rng _ _ _ HOLE) as [B _]. ceil. lia.
      - intros a Ha NE. destruct (M2W a Ha NE) as [[A|[A|[A|(rr & Hrr & NK & A)]]]|HOLE].
        + left. unfold AMSTK in A. lia.
        + right; right; left. exact A.
        + right; right; right. exact A.
        + right; left. exact (nongroup_nonapp L d s2 rr a W2 Hrr NK A).
        + right; left. exact (am_holeR_nonapp s2 L [] a W2 HOLE).
      - rewrite F2. kept_rw K1. reflexivity.
      - kept_rw K2. kept_rw K1. reflexivity.
      - kept_rw K2. kept_rw K1. reflexivity.
      - kept_rw K2. kept_rw K1. reflexivity.
      - kept_rw K2. kept_rw K1. reflexivity.
      - kept_rw K2. kept_rw K1. reflexivity.
      - eapply keeps_big; [eapply keeps_big; [exact KB | exact K1 | reflexivity] | exact K2 | reflexivity]. }
    assert (NJ2 : nojunk s2).
    { intros x k o Hx Hk E. rewrite Eslot in E. unfold is_group in Hx. rewrite Egrp in Hx.
      apply (NJ1 x k o Hx); [|exact E]. unfold g_lastidx, g_W in *. rewrite (Emg x Hx) in Hk. exact Hk. }
    assert (SIDE2 : bo = true -> bi = true \/ agf s2).
    { intros Hbo. destruct (SIDE Hbo) as [Hbi|AGF]; [left; exact Hbi | right].
      intros g Hg. unfold is_group in Hg. rewrite Egrp in Hg. rewrite (Emg g Hg). exact (AGF g Hg). }
    apply (L_G_cont s2 M2 mdl2 r2 m P2 NJ2 ltac:(rewrite Elim, EL; reflexivity) ltac:(rewrite Ealist; exact Hnil) Um Zm ltac:(rewrite <- EL; exact NLm2) SIDE2 F10
             ltac:(kept_rw K2; kept_rw K1; exact Q18) ltac:(kept_rw K2; exact E19) ltac:(kept_rw K2; exact E24) ltac:(kept_rw K2; exact E25)).
    - intros rr GB LE SD. exact (HL_N s2 M2 mdl2 rr m (gcnt s2) GB LE SD).
    - intros rr GB GT. exact (HL_M s2 M2 mdl2 rr m (gcnt s2) GB GT).
  Qed.
End ASG.
End UbMhASlotKG.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKM. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount.UbMhCountSpec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.UbMhASpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA UbMhASlotKB OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKM UbMhASlotKG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ASK.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Hypothesis HAM : AM_SPEC3.

  Section Body.
    Variables (st : mst) (L : list (Z * Z)) (M : mem) (mdl : Model)
              (regs : bvmap 5 word) (rom : word -> option byte) (sp sc req : Z) (d : nat)
              (F : kfam) (bi bo : bool).
    Hypothesis HL : kfam_laws RSEGS F.
    Hypothesis SIDE : bo = true -> bi = true \/ agf st.
    Hypothesis HWF : WF st L.
    Hypothesis HREP : REP st M.
    Hypothesis HLG : LEDGER st (m_vmmaps mdl).
    Hypothesis NJ : nojunk st.
    Hypothesis Hh : m_halted mdl = None.
    Hypothesis Hlz : m_vm_lazy mdl = [].
    Hypothesis Hmat : m_vm_materialized mdl = [].
    Hypothesis Hsc : 0 <= sc < 48.
    Hypothesis Hd : dle (dbound (16 * size_class sc)) d.
    Hypothesis Hlimbo : zlen (s_limbo st) + Z.of_nat d + 1 <= 8.
    Hypothesis Hreq : 0 <= req /\ req + 4 <= 16 * size_class sc.
    Hypothesis HBUD : PHI L + MBASE <= vm_limit (m_vmmaps mdl).
    Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
    Hypothesis R11 : getr regs 11 = Z_to_bv 64 req.
    Hypothesis R2 : getr regs 2 = Z_to_bv 64 sp.
    Hypothesis Rra : ret_ok (getr regs 1).
    Hypothesis R4 : getr regs 4 = Z_to_bv 64 TPV.
    Hypothesis Hsp : CEIL + ASSTK d <= sp /\ sp < 2 ^ 64.
    Hypothesis DEF : defined M (sp - ASSTK d) sp.
    Hypothesis HQ : forall c', as_ok st L sc req d sp regs M mdl rom c' -> kfx F bi c'.
    Hypothesis HQF : forall c', as_fail st L sc d sp regs M mdl rom c' -> Kf F c'.
    Hypothesis IHd : forall d', (d' < d)%nat -> AS_SPEC3 d'.

    #[local] Notation PT := (pt st L M mdl regs sp sc d).
    #[local] Notation PTE := (ptE st L M mdl regs sp sc d).
    #[local] Notation GBR := (gbr st L M mdl regs sp sc req d).

    (* [comment removed for export] *)
    Lemma LE : forall s1 Mc mdl1 r g idx,
      PTE s1 Mc mdl1 r -> s_limbo s1 = s_limbo st ->
      head_of (s_alist s1 sc) = g -> is_group s1 g -> g_sc s1 g = sc -> 0 <= idx <= g_lastidx s1 g ->
      s_slot s1 g idx = SJunk 0 -> only_junk s1 g idx -> req + 4 <= g_stride s1 g -> (16 * size_class sc <= g_stride s1 g \/ 4080 <= g_stride s1 g) ->
      getr r 10 = Z_to_bv 64 idx ->
      kat RSEGS (mkCfg (mkst r (0x67b10%bv : word) Mc rom) mdl1) (kfx F bi).
    Proof. intros. eapply (UbMhASlotKA.L_E st L M mdl regs rom sp sc req (kfx F bi) d); eassumption. Qed.

    Lemma LN : forall s2 M2 mdl2 r m cnt, GBR s2 M2 mdl2 r m cnt -> 16 * size_class sc * cnt + 16 <= 2048 ->
      (bo = true -> bi = true \/ agf s2) ->
      kat RSEGS (mkCfg (mkst r (0x675c0%bv : word) M2 rom) mdl2) (kfx F bo).
    Proof. intros. eapply (UbMhASlotKN.L_N st L M mdl regs rom sp sc req d F bi bo); try eassumption. exact LE. Qed.

    Lemma LM : forall s2 M2 mdl2 r m cnt, GBR s2 M2 mdl2 r m cnt -> 2048 < 16 * size_class sc * cnt + 16 ->
      kat RSEGS (mkCfg (mkst r (0x6757c%bv : word) M2 rom) mdl2) (kfx F bo).
    Proof.
      intros. eapply (UbMhASlotKM.L_M st L M mdl regs rom sp sc req d F bi bo); try eassumption.
      intros s1 Mc mdl1 r' g idx P _. exact (LE s1 Mc mdl1 r' g idx P).
    Qed.

    Lemma LG : forall s1 Mc mdl1 r,
      PT s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st -> s_alist s1 sc = [] -> getr r 18 = Z_to_bv 64 req ->
      (bo = true -> bi = true \/ agf s1) ->
      kat RSEGS (mkCfg (mkst r (0x67490%bv : word) Mc rom) mdl1) (kfx F bo).
    Proof. intros. eapply (UbMhASlotKG.L_G st L M mdl regs rom sp sc req d F bi bo); try eassumption; [exact LN | exact LM]. Qed.
  End Body.

  (* [comment removed for export] *)
  Lemma as_step : forall d, (forall d', (d' < d)%nat -> AS_SPEC3 d') -> AS_SPEC3 d.
  Proof.
    intros d IHd F bi bo st L M mdl regs rom sp sc req HL SIDE HWF HREP HLG NJ Hh Hlz Hmat Hsc Hd Hlimbo Hreq HBUD R10 R11 R2 Rra R4 Hsplo Hsphi DEF HQ HQF.
    assert (Hsp : CEIL + ASSTK d <= sp /\ sp < 2 ^ 64) by (split; assumption).
    apply (kfx_of_kat F HL bo). unfold AS_ENTRY. replace (Z_to_bv 64 0x672b0) with (0x672b0%bv : word) by (apply bv_eq; reflexivity).
    assert (LGx : forall s1 Mc mdl1 r,
      pt st L M mdl regs sp sc d s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st -> s_alist s1 sc = [] -> getr r 18 = Z_to_bv 64 req ->
      (bo = true -> bi = true \/ agf s1) ->
      kat RSEGS (mkCfg (mkst r (0x67490%bv : word) Mc rom) mdl1) (kfx F bo)).
    { intros. eapply (LG st L M mdl regs rom sp sc req d F bi bo); eassumption. }
    destruct bo.
    - destruct bi.
      + (* [comment removed for export] *)
        eapply (UbMhASlotKB.as_body st L M mdl regs rom sp sc req (kfx F true) d); try eassumption.
        intros s1 Mc mdl1 r P NJ1 EL Hnil A18. apply (LGx s1 Mc mdl1 r P NJ1 EL Hnil A18). intros _. left. reflexivity.
      + (* [comment removed for export] *)
        destruct (SIDE eq_refl) as [X|AGF]; [discriminate X|].
        eapply (UbMhASlotKB.as_body_agf st L M mdl regs rom sp sc req (kfx F true) d); try eassumption.
        intros s1 Mc mdl1 r P NJ1 EL Hnil A18 AG1. apply (LGx s1 Mc mdl1 r P NJ1 EL Hnil A18). intros _. right. exact AG1.
    - (* [comment removed for export] *)
      eapply (UbMhASlotKB.as_body st L M mdl regs rom sp sc req (kfx F false) d); try eassumption.
      + intros c' Hc. apply (kfx_mono RSEGS F HL bi false c'); [intros X; discriminate X | exact (HQ c' Hc)].
      + intros s1 Mc mdl1 r P NJ1 EL Hnil A18. apply (LGx s1 Mc mdl1 r P NJ1 EL Hnil A18). intros X. discriminate X.
  Qed.

  Theorem alloc_slot_run3 : forall d, AS_SPEC3 d.
  Proof.
    induction d as [d IH] using (well_founded_induction Wf_nat.lt_wf). apply as_step. exact IH.
  Qed.
End ASK.
