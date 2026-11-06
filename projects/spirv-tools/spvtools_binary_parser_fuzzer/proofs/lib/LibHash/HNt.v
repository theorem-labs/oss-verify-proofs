(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFind OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtCtx OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtA.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.S1_code_67e94_68324.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module HNtF.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFind OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtCtx OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtA OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.S1_code_67e94_68324.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
Local Ltac lia ::= pe3_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition NT_PN : Z := 0x682f4.
Definition STOPSF : list Z := [NT_PN; NT_EMPTY; NT_SIZE; NT_EXIT].

#[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

Section NtF.
Context {AC : AllocCeiling}.

  Variables (L : Layout) (MI : MallocIface SEGS L) (ST : StaticsIface SEGS L) (NEW_STACK DEL_STACK : Z).
  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp parser key bl bc : Z) (val : Z * Z * Z) (v2 : Z) (ents : list (Z * (Z * (Z * Z * Z)))) (K : TSet).
  Variable C : @ntctx AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K.
  #[local] Abbreviation NTS := (NT_STACK NEW_STACK DEL_STACK).
  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI (c_HLimg_lo C) (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST (c_HLimg_lo C) (c_HLrw_img C) (c_HLrelro_img C) (c_HLrw_relro C) (c_HLerr_rw C)).
  #[local] Abbreviation ro_clear_via_eff' := (ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation agree_block_via_eff' := (agree_block_via_eff L MI (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation own_sx_via_eff' := (own_sx_via_eff L MI ST (c_HLrw_img C)).
  #[local] Abbreviation hi_unowned' := (hi_unowned L MI (c_HLimg_lo C) (c_HLrw_img C)).
  #[local] Abbreviation obj := (parser + 136).
  #[local] Abbreviation sent := (parser + 152).
  #[local] Abbreviation W := (Wnt NEW_STACK DEL_STACK sp).
  #[local] Abbreviation base_ok := (nt_base_ok L R0 sp parser val v2).
  #[local] Abbreviation pframe := (nt_pframe sp parser key).
  #[local] Abbreviation SPF := (sp_facts C).
  #[local] Abbreviation BCF := (bc_facts C).
  #[local] Ltac ctx := ntctx_pose C.

  #[local] Abbreviation core := (@HNtA.core AC L MI ST NEW_STACK DEL_STACK A0 s R0 model0 sp parser key val v2).

  Lemma finish : forall (fx1 : FPState) p A M model R (bl2 bc2 : Z) (ents2 ents' : list ent) (rh : bool) (F : Z -> Prop),
    ainv MI A M model -> mstd model -> m_fs model = m_fs model0 -> m_fds model = m_fds model0 -> sx_inv ST s M -> frm_zero (@fp_csr fx1) ->
    base_ok R -> getr R 25%bv = Z_to_bv 64 p -> getr R 27%bv = Z_to_bv 64 (t3c val) ->
    cell8 SEGS M (obj + 24) (Zlength ents2) -> defined M obj 40 -> 0 <= Zlength ents2 < 2 ^ 60 ->
    defined M p 32 -> defined M (sp + 8) 8 -> 0 < p -> p + 32 <= alloc_ceiling -> In (p, 32) (live MI A) ->
    (forall M', (forall a : word, ~ (obj + 24 <= bv_unsigned a < obj + 32) -> ~ (p + 20 <= bv_unsigned a < p + 32) -> M' a = M a) ->
                (forall a : word, M a <> None -> M' a <> None) ->
                cell8 SEGS M' (obj + 24) (Zlength ents2 + 1) -> nval32 SEGS M' p val ->
                umapx MI 32 (nval32 SEGS) A M' obj bl2 bc2 ents') ->
    In (p, (key, val)) ents' -> Permutation ents' ((p, (key, val)) :: ents) ->
    (rh = false -> bl2 = bl /\ bc2 = bc) -> (rh = true -> (bc = 0 \/ Zlength ents = bc) /\ bc2 = bseq_next bc) ->
    lapply (live MI A0) (LAdd p 32 :: (if rh then LAdd bl2 (8 * bc2) :: (if bc =? 0 then [] else [LDel bl]) else [])) (live MI A) ->
    eff MI A0 A M0 M W F -> (forall a, F a -> umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl2 bc2 ents' a \/ (sp + 8 <= a < sp + 16)) ->
    (forall a, F a -> ~ in_ranges (ly_img L) a) ->
    srealizes SEGS (cfg fx1 R NT_SIZE M model) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros fx1 p A M model R bl2 bc2 ents2 ents' rh F AI MS Hfs Hfds SX FZ B Q25 Q27 Csz HDEF Hszr DEFp DEF8 Hp0 Hpc Hpl HU Hin PERM Hrf Hrt LAP EFF HF FOFF.
    destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
    pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs). unfold cell8 in Csz.
    destruct (live_facts' A M model p 32 AI Hpl) as (_ & _ & _ & Hpall).
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 (t3a val); Z_to_bv 64 v2; Z_to_bv 64 (t3c val); Z_to_bv 64 (Zlength ents2)]).
    assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (21%bv, EVar 35); (18%bv, EVar 36); (27%bv, EVar 37)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xruns HR HK 100%nat STOPSF (SCR [] [EVar 38] []) 50%N.
    { split_scs; try sc_auto1; sc_so; first [eapply (defined_sub _ _ _ _ _ HDEF); lia | eapply (defined_sub _ _ _ _ _ DEFp); lia]. }
    postrun. rewrite w_add by lia. rewrite (w2lb4_low v2), Hv2m.
    set (M' := wbytes (wbytes (wbytes (wbytes M _ _) _ _) _ _) _ _).
    assert (HMw : forall a : word, ~ (obj + 24 <= bv_unsigned a < obj + 32) -> ~ (p + 20 <= bv_unsigned a < p + 32) -> M' a = M a).
    { intros a Ha Hb. pose proof (u64_range a). unfold M'.
      rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; try (change (Z.of_nat 8) with 8); try (change (Z.of_nat 4) with 4); lia. }
    assert (HMg : forall a : word, M a <> None -> M' a <> None) by (intros a Ha; unfold M'; repeat apply wbytes_grows; exact Ha).
    assert (Csz' : cell8 SEGS M' (obj + 24) (Zlength ents2 + 1)) by (unfold M', cell8; cellpeel).
    assert (Hnv : nval32 SEGS M' p val).
    { generalize Hv1 Hv2 Hv3. clear HU. destruct val as [[va vb] vc]. unfold nval32, cell4, M'. cbn [t3a t3b t3c fst snd]. intros Hva Hvb Hvc.
      split; [|split]; cellpeel. }
    assert (AI' : ainv MI A M' model).
    { eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
      intros x Ho. pose proof (u64_range x). apply HMw; intros Hx; [exact (hi_unowned' A M model (bv_unsigned x) AI ltac:(lia) Ho) | exact (proj1 (Hpall (bv_unsigned x) ltac:(lia)) Ho)]. }
    assert (EF' : eff MI A A M M' W (fun a => obj + 24 <= a < obj + 32 \/ p + 20 <= a < p + 32)).
    { apply eff_store; [| exact HMg]. intros x HFx _. apply HMw; intros Hx; apply HFx; [left | right]; exact Hx. }
    assert (FOFF' : forall a, (obj + 24 <= a < obj + 32 \/ p + 20 <= a < p + 32) -> ~ in_ranges (ly_img L) a).
    { intros a [Ha | Ha] Hi; [pose proof (HLimg_lo _ Hi); lia | exact (live_offimg' A M model p 32 a AI Hpl ltac:(lia) Hi)]. }
    apply (CONT fx1 A R' M' model p bl2 bc2 ents' true rh AI' MS Hfs Hfds).
    - eapply (sx_inv_via_eff' s A A M M' model W _ SX AI EF'); [| exact Herr_sx | exact FOFF' | unfold Wnt; cbn; lia].
      exact (own_sx_via_eff' A0 A M0 M W F EFF Hown_sx FOFF).
    - exact FZ.
    - apply (kept_of_base C); [nt_base_from HR' B | rreg HR' 27%bv Q; exact Q].
    - rreg HR' 25%bv Q. exact Q.
    - exact (HU M' HMw HMg Csz' Hnv).
    - exact Hin.
    - intros HT. discriminate HT.
    - intros _. exact PERM.
    - exact Hrf. - exact Hrt.
    - cbn [app]. exact LAP.
    - unfold Wnt in EFF |- *. eapply eff_weaken; [eapply eff_trans; [exact EFF | exact EF' | intros a Ha; eapply hi_unowned'; [exact AI' | unfold W_of in Ha; cbn in Ha; lia]]|].
      intros a [Ha | [Ha | Ha]]; [exact (HF a Ha) | left; left; lia | right; left; right; right; exists p; split; [apply in_map_iff; exists (p, (key, val)); split; [reflexivity | exact Hin] | lia]].
    - intros i Hi. apply HMg. apply DEF8. exact Hi.
  Qed.

  Lemma umapx_link : forall A M M' (p bl2 bc2 : Z) (v : Z * Z * Z) (l1 l2 : list ent),
    umapx MI 32 (nval32 SEGS) A M obj bl2 bc2 (l1 ++ l2) -> bc2 <> 0 -> Zlength (l1 ++ l2) + 1 <= bc2 ->
    In (p, 32) (live MI A) -> 0 < p -> p + 32 <= alloc_ceiling -> p mod 16 = 0 ->
    (forall q m, In (q, m) (umap_blocks 32 bl2 bc2 (l1 ++ l2)) -> apart p 32 q m) ->
    cell8 SEGS M' p (hdaddr l2) -> cell8 SEGS M' (p + 8) key -> cell4 SEGS M' (p + 16) key -> nval32 SEGS M' p v ->
    cell8 SEGS M' (lasta (obj + 16) l1) p -> cell8 SEGS M' (obj + 24) (Zlength (l1 ++ l2) + 1) ->
    (forall x : word, M x <> None -> M' x <> None) ->
    (forall a, umap_foot 32 obj bl2 bc2 (l1 ++ l2) a -> ~ (lasta (obj + 16) l1 <= a < lasta (obj + 16) l1 + 8) -> ~ (obj + 24 <= a < obj + 32) ->
               ~ (bl2 <= a < bl2 + 8 * bc2) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall i, 0 <= i < bc2 -> exists b', cell8 SEGS M' (bl2 + 8 * i) b' /\ bucket_ok obj bc2 (l1 ++ (p, (key, v)) :: l2) i b') ->
    umapx MI 32 (nval32 SEGS) A M' obj bl2 bc2 (l1 ++ (p, (key, v)) :: l2).
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros A M M' p bl2 bc2 v l1 l2 U Hbc Hload Hpl Hp0 Hpc Hpal Hpa Cn Ch Ck Cv Cpred Csz HG HM HB.
    pose proof ceiling_lt as Hcl. destruct SPF as (_ & Hsplo & Hsphi & Hn16 & _ & _ & Hs1 & _).
    pose proof (proj1 (nf_key _ _ _ _ _ _ _ _ _ NF)) as Hkr. cbn in Hkr.
    destruct U as [HD Hoal Holo Hohi Hbseq Hload0 Hblive Hblal Hbllo Hblhi Hblobj Hbkt Hndup Hch Hnode Hapart].
    destruct HD as [Cbl Cbc Cp1 Csz0 Cmlf Cdef].
    pose proof (Hbllo Hbc) as Hbl0. pose proof (Hblobj Hbc) as Hblo.

    assert (NF' : forall q k v', In (q, (k, v')) (l1 ++ l2) -> 0 < q /\ q + 32 <= 2 ^ 47 /\ apart q 32 obj 40 /\ apart q 32 bl2 (8 * bc2) /\ apart p 32 q 32).
    { intros q k v' Hin. destruct (Hnode q k v' Hin) as (_ & Hq0 & Hq1 & _ & _ & _ & _ & _ & Hqo & Hqb).
      split; [exact Hq0|]. split; [exact Hq1|]. split; [exact Hqo|]. split; [exact (Hqb Hbc)|].
      apply Hpa. unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (q, (k, v')). split; [reflexivity | exact Hin]. }

    assert (Hpred : (l1 = [] /\ lasta (obj + 16) l1 = obj + 16)
                    \/ (exists r y, l1 = r ++ [y] /\ lasta (obj + 16) l1 = fst y /\ In y (l1 ++ l2))).
    { destruct l1 as [|e l1'] eqn:HL; [left; split; reflexivity | right].
      exists (removelast l1), (last l1 (0, (0, (0, 0, 0)))). rewrite <- HL.
      assert (Hne : l1 <> []) by (rewrite HL; discriminate).
      split; [exact (app_removelast_last _ Hne)|]. split; [rewrite (app_removelast_last (0, (0, (0, 0, 0))) Hne) at 1; rewrite lasta_snoc; reflexivity|].
      apply in_app_iff. left. rewrite (app_removelast_last (0, (0, (0, 0, 0))) Hne) at 2. apply in_app_iff. right. left. reflexivity. }

    assert (AGt : forall q k v', In (q, (k, v')) (l1 ++ l2) -> agree_on M M' (q + 8) 24).
    { intros q k v' Hin. destruct (NF' q k v' Hin) as (Hq0 & Hq1 & Hqo & Hqb & Hqp). intros i Hi. apply HM.
      - right. right. exists q. split; [apply in_map_iff; exists (q, (k, v')); split; [reflexivity | exact Hin] | lia].
      - destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [unfold apart in Hqo; lia|].
        destruct y as [yq [yk yv]]. cbn. destruct (Z.eq_dec yq q) as [->|Hne]; [lia|].
        pose proof (Hapart yq q ltac:(apply in_map_iff; exists (yq, (yk, yv)); split; [reflexivity | exact Hy]) ltac:(apply in_map_iff; exists (q, (k, v')); split; [reflexivity | exact Hin]) Hne) as Hap.
        unfold apart in Hap. lia.
      - unfold apart in Hqo. lia.
      - unfold apart in Hqb. lia. }
    assert (AGn : forall q k v', In (q, (k, v')) (l1 ++ l2) -> q <> lasta (obj + 16) l1 -> agree_on M M' q 8).
    { intros q k v' Hin Hne. destruct (NF' q k v' Hin) as (Hq0 & Hq1 & Hqo & Hqb & Hqp). intros i Hi. apply HM.
      - right. right. exists q. split; [apply in_map_iff; exists (q, (k, v')); split; [reflexivity | exact Hin] | lia].
      - destruct Hpred as [[_ HL] | (r & y & HL & Hly & Hy)]; [rewrite HL in *; unfold apart in Hqo; lia|].
        rewrite Hly in *. destruct y as [yq [yk yv]]. cbn in *.
        pose proof (Hapart yq q ltac:(apply in_map_iff; exists (yq, (yk, yv)); split; [reflexivity | exact Hy]) ltac:(apply in_map_iff; exists (q, (k, v')); split; [reflexivity | exact Hin]) (not_eq_sym Hne)) as Hap.
        unfold apart in Hap. lia.
      - unfold apart in Hqo. lia.
      - unfold apart in Hqb. lia. }
    assert (Hlen : Zlength (l1 ++ (p, (key, v)) :: l2) = Zlength (l1 ++ l2) + 1).
    { unfold Zlength. rewrite !length_app. cbn [length]. lia. }
    assert (HpN : ~ In p (map fst (l1 ++ l2))).
    { intros Hin. apply in_map_iff in Hin. destruct Hin as ([q [k v']] & Hq & Hin). cbn in Hq. subst q.
      destruct (NF' p k v' Hin) as (_ & _ & _ & _ & Hap). unfold apart in Hap. lia. }
    pose proof Hndup as NDL. apply base.NoDup_ListNoDup in NDL.
    constructor.
    - constructor.
      + eapply cellw_agree; [exact Cbl | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
        destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [lia|]. destruct y as [yq [yk yv]]. destruct (NF' yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
      + eapply cellw_agree; [exact Cbc | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
        destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [lia|]. destruct y as [yq [yk yv]]. destruct (NF' yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
      + destruct Hpred as [[HL Hla] | (r & y & HL & Hla & Hy)].
        * rewrite HL in *. cbn [app hdaddr]. rewrite Hla in Cpred. exact Cpred.
        * replace (hdaddr (l1 ++ (p, (key, v)) :: l2)) with (hdaddr (l1 ++ l2)) by (rewrite HL, <- !app_assoc; destruct r as [|[? ?] ?]; reflexivity).
          eapply cellw_agree; [exact Cp1 | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
          rewrite Hla. destruct y as [yq [yk yv]]. destruct (NF' yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
      + rewrite Hlen. exact Csz.
      + eapply cellw_agree; [exact Cmlf | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
        destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [lia|]. destruct y as [yq [yk yv]]. destruct (NF' yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
      + intros i Hi. apply HG. apply Cdef. exact Hi.
    - exact Hoal. - exact Holo. - exact Hohi. - exact Hbseq.
    - rewrite Hlen. exact Hload.
    - exact Hblive. - exact Hblal. - exact Hbllo. - exact Hblhi. - exact Hblobj.
    - exact HB.
    - rewrite map_app. cbn [map fst]. apply (proj2 (base.NoDup_ListNoDup _)). apply (proj2 (NoDup_Add (Add_app p _ _))).
      rewrite <- map_app. split; [exact NDL | exact HpN].
    -
      apply lnk_chain. apply lnk_chain in Hch. apply lnk_app in Hch. destruct Hch as [L1 L2].
      apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- hdaddr_hda; exact Cn |]].
      + destruct Hpred as [[HL _] | (r & y & HL & Hla & Hy)]; [rewrite HL; exact I|].
        rewrite HL in L1 |- *. apply lnk_app in L1. destruct L1 as [L1 _]. apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- Hla; exact Cpred | exact I]].
        assert (NDl1 : List.NoDup (map fst l1)) by (rewrite map_app in NDL; exact (NoDup_app_remove_r _ _ NDL)). rewrite HL in NDl1.
        eapply lnk_agree; [exact L1 | |].
        * intros a Ha. destruct a as [q [k v']]. apply (AGn q k v'); [apply in_app_iff; left; rewrite HL; apply in_app_iff; left; exact Ha|].
          rewrite Hla. exact (nodup_app_ne r [y] (q, (k, v')) y NDl1 Ha (or_introl eq_refl)).
        * intros a Ha. destruct a as [q [k v']]. destruct (NF' q k v' ltac:(apply in_app_iff; left; rewrite HL; apply in_app_iff; left; exact Ha)) as (Hq0 & Hq1 & _). cbn. lia.
      + eapply lnk_agree; [exact L2 | |].
        * intros a Ha. destruct a as [q [k v']]. apply (AGn q k v'); [apply in_app_iff; right; exact Ha|].
          destruct Hpred as [[HL Hla] | (r & y & HL & Hla & Hy)]; rewrite Hla.
          -- destruct (NF' q k v' ltac:(apply in_app_iff; right; exact Ha)) as (_ & _ & Hqo & _). unfold apart in Hqo. lia.
          -- apply not_eq_sym. apply (nodup_app_ne l1 l2 y (q, (k, v')) NDL); [rewrite HL; apply in_app_iff; right; left; reflexivity | exact Ha].
        * intros a Ha. destruct a as [q [k v']]. destruct (NF' q k v' ltac:(apply in_app_iff; right; exact Ha)) as (Hq0 & Hq1 & _). cbn. lia.
    -
      intros q k v' Hin. apply in_app_iff in Hin. destruct Hin as [Hin | [Hin | Hin]].
      2: { injection Hin as <- <- <-.
           split; [exact Hpl|]. split; [exact Hp0|]. split; [lia|]. split; [exact Hpal|]. split; [exact Ch|]. split; [exact Ck|]. split; [lia|].
           split; [exact Cv|]. split; [unfold apart; lia|]. intros _. apply Hpa. unfold umap_blocks. destruct (Z.eqb_spec bc2 0); [lia|]. apply in_app_iff. left. left. reflexivity. }
      all: assert (Hin' : In (q, (k, v')) (l1 ++ l2)) by (apply in_app_iff; tauto).
      all: destruct (Hnode q k v' Hin') as (Hlv & Hq0 & Hq1 & Hqal & Hh & Hk & Hkr' & Hv & Hqo & Hqb); pose proof (AGt q k v' Hin') as AG.
      all: split; [exact Hlv|]; split; [exact Hq0|]; split; [exact Hq1|]; split; [exact Hqal|].
      all: split; [eapply cellw_agree; [exact Hh | eapply agree_on_sub; [exact AG | lia | cbn; lia] | lia | cbn; lia]|].
      all: split; [eapply cellw_agree; [exact Hk | eapply agree_on_sub; [exact AG | lia | cbn; lia] | lia | cbn; lia]|].
      all: split; [exact Hkr'|].
      all: split; [eapply nval32_agree; [exact Hv | eapply agree_on_sub; [exact AG | lia | cbn; lia] | lia | lia]|].
      all: split; [exact Hqo | exact Hqb].
    -
      intros q q' Hq Hq' Hne. rewrite map_app in Hq, Hq'. cbn [map fst] in Hq, Hq'.
      assert (Hcase : forall z, In z (map fst l1 ++ p :: map fst l2) -> z = p \/ In z (map fst (l1 ++ l2))).
      { intros z Hz. rewrite map_app. apply in_app_iff in Hz. destruct Hz as [Hz|[<-|Hz]]; [right; apply in_app_iff; left; exact Hz | left; reflexivity | right; apply in_app_iff; right; exact Hz]. }
      destruct (Hcase q Hq) as [-> | Hq2]; destruct (Hcase q' Hq') as [-> | Hq2'].
      + exfalso. exact (Hne eq_refl).
      + apply in_map_iff in Hq2'. destruct Hq2' as ([z [k v']] & Hz & Hin). cbn in Hz. subst z. exact (proj2 (proj2 (proj2 (proj2 (NF' q' k v' Hin))))).
      + apply in_map_iff in Hq2. destruct Hq2 as ([z [k v']] & Hz & Hin). cbn in Hz. subst z.
        pose proof (proj2 (proj2 (proj2 (proj2 (NF' q k v' Hin))))) as Hap. unfold apart in *. lia.
      + exact (Hapart q q' Hq2 Hq2' Hne).
  Qed.

  Lemma umap_foot_mono : forall bl2 bc2 (l1 l2 : list ent) e a,
    umap_foot 32 obj bl2 bc2 (l1 ++ l2) a -> umap_foot 32 obj bl2 bc2 (l1 ++ e :: l2) a.
  Proof using parser.
    intros bl2 bc2 l1 l2 e a [H|[H|(q & Hq & Ha)]]; [left; exact H | right; left; exact H | right; right].
    exists q. split; [|exact Ha]. rewrite map_app in Hq |- *. cbn. apply in_app_iff in Hq. apply in_app_iff. destruct Hq; [left | right; right]; assumption.
  Qed.

  Lemma phaseF_pn : forall (fx1 : FPState) p A M model R (bl2 bc2 : Z) (ents2 : list ent) (rh : bool) (b : Z) (F : Z -> Prop),
    core p A M model R -> frm_zero (@fp_csr fx1) -> bc2 <> 0 -> Zlength ents + 1 <= bc2 ->
    getr R 22%bv = Z_to_bv 64 bc2 -> getr R 12%bv = Z_to_bv 64 b -> getr R 27%bv = Z_to_bv 64 (t3c val) ->
    bucket_ok obj bc2 ents2 (hmod key bc2) b -> b <> 0 ->
    umapx MI 32 (nval32 SEGS) A M obj bl2 bc2 ents2 -> Permutation ents2 ents ->
    (forall q m, In (q, m) (umap_blocks 32 bl2 bc2 ents2) -> apart p 32 q m) ->
    (rh = false -> bl2 = bl /\ bc2 = bc) -> (rh = true -> (bc = 0 \/ Zlength ents = bc) /\ bc2 = bseq_next bc) ->
    lapply (live MI A0) (LAdd p 32 :: (if rh then LAdd bl2 (8 * bc2) :: (if bc =? 0 then [] else [LDel bl]) else [])) (live MI A) ->
    eff MI A0 A M0 M W F -> (forall a, F a -> p <= a < p + 32 \/ umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl2 bc2 ents2 a \/ (sp + 8 <= a < sp + 16)) ->
    (forall a, F a -> ~ in_ranges (ly_img L) a) ->
    srealizes SEGS (cfg fx1 R NT_PN M model) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros fx1 p A M model R bl2 bc2 ents2 rh b F CO FZ Hbc2 Hload Q22 Q12 Q27 Hbok Hbnz U2 PERM2 Hpa Hrf Hrt LAP EFF HF FOFF.
    destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
    pose proof (proj1 (nf_key _ _ _ _ _ _ _ _ _ NF)) as Hkr. cbn in Hkr.
    destruct CO as [AI MS Hfs Hfds SX B Q23 Q25 FR DEF8 DEFW Hp0 Hpc Hpal Hpl Hpnew Cnh Cnk DEFp].
    assert (Hlen : Zlength ents2 = Zlength ents) by (unfold Zlength; rewrite (Permutation_length PERM2); reflexivity).
    pose proof (h_def (u_hdr U2)) as HDEF. pose proof (h_size (u_hdr U2)) as Csz.

    assert (HS : exists l1 l2 q0, ents2 = l1 ++ l2 /\ lasta (obj + 16) l1 = b /\ q0 = hdaddr l2 /\ cell8 SEGS M b q0
                 /\ 0 < b /\ b + 8 <= 2 ^ 47 /\ defined M b 8 /\ apart p 32 b 8 /\ (forall a, b <= a < b + 8 -> ~ owned MI A a)
                 /\ (b + 8 <= alloc_ceiling \/ b = obj + 16)
                 /\ (forall a, b <= a < b + 8 -> umap_foot 32 obj bl2 bc2 ents2 a)
                 /\ (l1 = [] -> hmod key bc2 = hmod (hdkey ents2) bc2)).
    { destruct Hbok as [Hb0 | [Hbn | (Hbs & Hne & Hch)]]; [exfalso; exact (Hbnz Hb0) | |].
      - destruct (in_split_ents _ b ents2 Hbn) as (l1 & kb & vb & l2 & HE).
        destruct (u_node U2 b kb vb ltac:(rewrite HE; apply in_app_iff; right; left; reflexivity)) as (Hlv & Hb0 & Hb1 & _ & _ & _ & _ & _ & Hbo & _).
        destruct (live_facts' A M model b 32 AI Hlv) as (_ & _ & Hbc & Hall).
        exists (l1 ++ [(b, (kb, vb))]), l2, (hdaddr l2). rewrite HE, <- app_assoc. cbn [app].
        split; [reflexivity|]. split; [rewrite lasta_snoc; reflexivity|]. split; [reflexivity|].
        split; [apply (chain_at _ M l1 b kb vb l2); rewrite <- HE; exact (u_chain U2)|].
        split; [lia|]. split; [lia|]. split; [intros i Hi; exact (proj2 (Hall (b + i) ltac:(lia)))|].
        split; [eapply (apart_sub' p 32 b 32); [apply Hpa; unfold umap_blocks; apply in_app_iff; right; apply in_map_iff; exists (b, (kb, vb)); split; [reflexivity | rewrite HE; apply in_app_iff; right; left; reflexivity] | lia]|].
        split; [intros a Ha; exact (proj1 (Hall a ltac:(lia)))|].
        split; [left; lia|].
        split; [intros a Ha; right; right; exists b; split; [rewrite <- HE; exact Hbn | lia]|].
        intros HL. destruct l1; discriminate HL.
      - exists (@nil ent), ents2, (hdaddr ents2). subst b.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (h_p1 (u_hdr U2))|].
        split; [lia|]. split; [lia|]. split; [eapply (defined_sub _ _ _ _ _ HDEF); lia|].
        split; [unfold apart; lia|]. split; [intros a Ha; apply (hi_unowned' A M model); [exact AI | lia]|].
        split; [right; reflexivity|]. split; [intros a Ha; left; lia|]. intros _. exact Hch. }
    destruct HS as (l1 & l2 & q0 & HE & Hla & -> & Cb & Hb0 & Hb1 & DEFb & Hpb & Hbown & Hblh & Hbfoot & Hch).
    unfold cell8 in Cb. pose proof (proj1 Cb) as Hq0r.
    pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 bc2; Z_to_bv 64 key; Z_to_bv 64 b; Z_to_bv 64 (t3c val); Z_to_bv 64 (hdaddr l2)]).
    assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (22%bv, EVar 35); (23%bv, EVar 36); (12%bv, EVar 37); (27%bv, EVar 38)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KDisj (SA (EVar 32) 0) (ELit 32) (SA (EVar 37) 0) (ELit 8)]).
    { repeat apply Forall_cons; try apply Forall_nil. eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | unfold apart in Hpb; lia]. }
    xruns HR HK 100%nat STOPSF (SCR [] [EVar 39] []) 50%N.
    { split_scs; try sc_auto1; sc_so; first [eapply (defined_sub _ _ _ _ _ DEFp); lia | eapply (defined_sub _ _ _ _ _ DEFb); lia]. }
    postrun.
    set (M2 := wbytes (wbytes M _ _) _ _).
    assert (HM2w : forall a : word, ~ (p <= bv_unsigned a < p + 8) -> ~ (b <= bv_unsigned a < b + 8) -> M2 a = M a).
    { intros a H1 H2. pose proof (u64_range a). unfold M2.
      rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
    assert (HM2g : forall a : word, M a <> None -> M2 a <> None) by (intros a Ha; unfold M2; repeat apply wbytes_grows; exact Ha).
    assert (AI2 : ainv MI A M2 model).
    { eapply (ai_frame MI); [exact AI | | exact HM2g | reflexivity | reflexivity].
      intros x Ho. pose proof (u64_range x). apply HM2w; intros Hx.
      - destruct (live_facts' A M model p 32 AI Hpl) as (_ & _ & _ & Hall). exact (proj1 (Hall (bv_unsigned x) ltac:(lia)) Ho).
      - exact (Hbown (bv_unsigned x) Hx Ho). }
    assert (Hfoot_p : forall a, umap_foot 32 obj bl2 bc2 ents2 a -> ~ (p <= a < p + 32)).
    { intros a Ha Hpa'. destruct (umap_foot_hb 32 obj bl2 bc2 ents2 a Ha) as [Hh | ([q m] & Hq & Hqa)]; [lia|]. cbn in Hqa.
      pose proof (Hpa q m Hq) as Hap. unfold apart in Hap.
      assert (Hm : 0 < m).
      { unfold umap_blocks in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
        - destruct (Z.eqb_spec bc2 0); [destruct Hq|]. destruct Hq as [Hq|[]]. injection Hq as <- <-. pose proof (u_bseq U2) as HB. unfold BSEQ in HB. cbn in HB. lia.
        - apply in_map_iff in Hq. destruct Hq as (e & He & _). injection He as _ <-. lia. }
      lia. }
    assert (FOFF2 : forall a, (p <= a < p + 8 \/ b <= a < b + 8) -> ~ in_ranges (ly_img L) a).
    { intros a [Ha | Ha] Hi.
      + exact (live_offimg' A M model p 32 a AI Hpl ltac:(lia) Hi).
      + pose proof (HLimg_lo _ Hi). destruct Hblh as [Hlow | Hhigh]; [| lia].
        destruct Hbok as [Hb0' | [Hbn | (Hbs & _)]]; [exact (Hbnz Hb0') | | lia].
        apply in_map_iff in Hbn. destruct Hbn as ([z [kz vz]] & Hz & Hin). cbn in Hz. subst z.
        exact (live_offimg' A M model b 32 a AI (proj1 (u_node U2 b kz vz Hin)) ltac:(lia) Hi). }
    assert (EF2 : eff MI A A M M2 W (fun a => p <= a < p + 8 \/ b <= a < b + 8)).
    { apply eff_store; [| exact HM2g]. intros x HFx _. apply HM2w; intros Hx; apply HFx; [left | right]; exact Hx. }
    eapply (finish fx1 p A M2 model R' bl2 bc2 ents2 (l1 ++ (p, (key, val)) :: l2) rh (fun a => F a \/ p <= a < p + 8 \/ b <= a < b + 8)).
    - exact AI2. - exact MS. - exact Hfs. - exact Hfds.
    - eapply (sx_inv_via_eff' s A A M M2 model W _ SX AI EF2); [exact (own_sx_via_eff' A0 A M0 M W F EFF Hown_sx FOFF) | exact Herr_sx | exact FOFF2 | unfold Wnt; cbn; lia].
    - exact FZ.
    - nt_base_from HR' B.
    - rreg HR' 25%bv Q. exact Q.
    - rreg HR' 27%bv Q. exact Q.
    - unfold M2, cell8. pose proof Csz as Csz'. unfold cell8 in Csz'. cellpeel.
    - intros i Hi. apply HM2g. apply HDEF. exact Hi.
    - pose proof (u_load U2). pose proof (u_bseq U2) as HB. unfold BSEQ in HB. cbn in HB. unfold Zlength in *. lia.
    - intros i Hi. apply HM2g. apply DEFp. exact Hi.
    - intros i Hi. apply HM2g. apply DEF8. exact Hi.
    - exact Hp0. - exact Hpc. - exact Hpl.
    -
      intros M' HM'w HM'g Csz' Hnv'. rewrite HE in U2, Hpa.
      eapply (umapx_link A M M' p bl2 bc2 val l1 l2 U2 Hbc2 ltac:(rewrite <- HE; lia) Hpl Hp0 Hpc Hpal Hpa).
      + assert (C2n : cell8 SEGS M2 p (hdaddr l2)) by (unfold M2, cell8; cellpeel).
        eapply cellw_agree; [exact C2n | | lia | cbn; lia]. intros i Hi. apply HM'w; rewrite u64_of_Z by lia; lia.
      + eapply cellw_agree; [exact Cnh | | lia | cbn; lia]. intros i Hi. rewrite HM'w by (rewrite u64_of_Z by lia; lia). apply HM2w; rewrite u64_of_Z by lia; unfold apart in Hpb; lia.
      + eapply cellw_agree; [exact Cnk | | lia | cbn; lia]. intros i Hi. rewrite HM'w by (rewrite u64_of_Z by lia; lia). apply HM2w; rewrite u64_of_Z by lia; unfold apart in Hpb; lia.
      + exact Hnv'.
      + rewrite Hla. assert (C2b : cell8 SEGS M2 b p) by (unfold M2, cell8; cellpeel).
        eapply cellw_agree; [exact C2b | | lia | cbn; lia]. intros i Hi. apply HM'w; rewrite u64_of_Z by lia; unfold apart in Hpb; lia.
      + rewrite <- HE. exact Csz'.
      + intros x Hx. apply HM'g, HM2g, Hx.
      + rewrite Hla. intros a Ha Hnb Hnsz Hnbl. pose proof (foot_low_or_high_gen C A M model bl2 bc2 _ a AI U2 Ha) as Har.
        pose proof (Hfoot_p a ltac:(rewrite HE; exact Ha)).
        rewrite HM'w by (rewrite u64_of_Z by lia; lia). apply HM2w; rewrite u64_of_Z by lia; [lia | exact Hnb].
      +
        intros i Hi. rewrite <- HE in *. destruct (u_bkt U2 i Hi) as (b' & Cb' & Hok'). exists b'. split.
        * pose proof (u_bl_lo U2 Hbc2). pose proof (u_bl_hi U2). pose proof (u_bl_obj U2 Hbc2) as Hblo.
          assert (Hpbl : apart p 32 bl2 (8 * bc2)).
          { apply Hpa. rewrite HE. unfold umap_blocks. destruct (Z.eqb_spec bc2 0); [lia|]. apply in_app_iff. left. left. reflexivity. }
          eapply cellw_agree; [exact Cb' | | lia | cbn; lia]. intros j Hj.
          rewrite HM'w by (rewrite u64_of_Z by lia; unfold apart in Hblo, Hpbl; lia).
          apply HM2w; rewrite u64_of_Z by lia.
          -- pose proof (Hfoot_p (bl2 + 8 * i + j) ltac:(right; left; split; [exact Hbc2 | lia])). lia.
          -- intros Hx. pose proof (Hbfoot (bl2 + 8 * i + j) Hx) as Hf.
             destruct Hf as [Hh | [[_ Hba] | (q & Hq & Hqa)]]; [unfold apart in Hblo; lia | | ].
             ++ unfold apart in Hblo. destruct Hblh as [Hlow | Hhigh]; [| lia].
                destruct Hbok as [Hb0' | [Hbn | (Hbs & _)]]; [exfalso; exact (Hbnz Hb0') | | lia].
                apply in_map_iff in Hbn. destruct Hbn as ([z [kz vz]] & Hz & Hin). cbn in Hz. subst z.
                destruct (u_node U2 b kz vz Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hqb). pose proof (Hqb Hbc2) as Hap. unfold apart in Hap. lia.
             ++ apply in_map_iff in Hq. destruct Hq as ([z [kz vz]] & Hz & Hin). cbn in Hz. subst z.
                destruct (u_node U2 q kz vz Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hqb). pose proof (Hqb Hbc2) as Hap. unfold apart in Hap. lia.
        * destruct Hok' as [H0 | [Hn | (Hs & Hne & Hi')]]; [left; exact H0 | right; left | right; right].
          -- rewrite HE in Hn. rewrite map_app in Hn |- *. cbn. apply in_app_iff in Hn. apply in_app_iff. destruct Hn; [left | right; right]; assumption.
          -- split; [exact Hs|]. split; [destruct l1; discriminate|]. rewrite Hi'. rewrite HE.
             destruct l1 as [|e l1']; [cbn [app hdkey fst snd]; pose proof (Hch eq_refl) as Hc; rewrite HE in Hc; cbn [app] in Hc; symmetry; exact Hc | reflexivity].
    - apply in_app_iff. right. left. reflexivity.
    - eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- HE. exact PERM2.
    - exact Hrf. - exact Hrt. - exact LAP.
    - eapply eff_trans; [exact EFF | exact EF2 | intros a Ha; eapply hi_unowned'; [exact AI2 | unfold W_of, Wnt in Ha; cbn in Ha; lia]].
    - intros a [Ha | [Ha | Ha]].
      + destruct (HF a Ha) as [H|[H|[H|H]]]; [right; left; right; right; exists p; split; [rewrite map_app; apply in_app_iff; right; left; reflexivity | lia] | left; exact H | right; left; rewrite HE in H; exact (umap_foot_mono _ _ _ _ _ _ H) | right; right; exact H].
      + right. left. right. right. exists p. split; [rewrite map_app; apply in_app_iff; right; left; reflexivity | lia].
      + right. left. pose proof (Hbfoot a Ha) as H. rewrite HE in H. exact (umap_foot_mono _ _ _ _ _ _ H).
    - intros a [Ha | Ha]; [exact (FOFF a Ha) | exact (FOFF2 a Ha)].
  Qed.

  Ltac fin5 FIN HR' extra wit Hj B :=
    eapply (FIN _ _ extra); [ wit | evs; nrw Hj; reflexivity | nt_base_from HR' B
      | let Q := fresh in rreg HR' 25%bv Q; exact Q
      | let Q := fresh in rreg HR' 27%bv Q; exact Q ].

  Ltac scE Hland Hj DEFp HDEF DEFbl :=
    split_scs;
    lazymatch goal with
    | |- sc_denot _ _ _ (SCStoreOk _ _) =>
        eapply sc_storeok; [evs; nrw Hj; reflexivity | lia | cbn [a_off]; lia | cbn [a_off]; lia
                          | cbn [a_off]; rewrite ?Z.add_0_r;
                            first [ lazymatch goal with |- defined _ ?a _ => match goal with D : defined _ a _ |- _ => eapply (defined_sub _ _ _ _ _ D); lia end end
                                  | eapply (defined_sub _ _ _ _ _ HDEF); lia | eapply (defined_sub _ _ _ _ _ DEFp); lia | eapply (defined_sub _ _ _ _ _ DEFbl); lia] ]
    | |- sc_denot _ _ _ (SCFlat _ _) => eapply sc_flat; [evs; nrw Hj; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]
    | |- sc_denot _ _ _ (SCBr _ _ _ _) => cbn [sc_denot]; evs; nrw Hj; rewrite ?Hland; rewrite ?br_ne, ?br_eq, ?br_ltu, ?br_geu, ?br_eq_sxw, ?br_ne_sxw by lia; bool_lia
    | |- sc_denot _ _ _ (SCReadBase _ _ _ _) =>
        first [ match goal with H : cellw _ _ _ _ _ |- _ =>
                  eapply (sc_read_cellw _ _ _ _ _ _ _ _ H); [first [apply N.le_refl | cbn; lia] | evs; nrw Hj; first [reflexivity | f_equal; lia] | evs; reflexivity] end
              | sc_auto1 ]
    | |- _ => sc_auto1
    end.

  Lemma phaseF_empty : forall (fx1 : FPState) p A M model R (bl2 bc2 : Z) (ents2 : list ent) (rh : bool) (F : Z -> Prop),
    core p A M model R -> frm_zero (@fp_csr fx1) -> bc2 <> 0 -> Zlength ents + 1 <= bc2 ->
    getr R 22%bv = Z_to_bv 64 bc2 -> getr R 10%bv = Z_to_bv 64 bl2 -> getr R 11%bv = Z_to_bv 64 (bl2 + 8 * hmod key bc2) ->
    getr R 27%bv = Z_to_bv 64 (t3c val) -> cell8 SEGS M (bl2 + 8 * hmod key bc2) 0 ->
    umapx MI 32 (nval32 SEGS) A M obj bl2 bc2 ents2 -> Permutation ents2 ents ->
    (forall q m, In (q, m) (umap_blocks 32 bl2 bc2 ents2) -> apart p 32 q m) ->
    (rh = false -> bl2 = bl /\ bc2 = bc) -> (rh = true -> (bc = 0 \/ Zlength ents = bc) /\ bc2 = bseq_next bc) ->
    lapply (live MI A0) (LAdd p 32 :: (if rh then LAdd bl2 (8 * bc2) :: (if bc =? 0 then [] else [LDel bl]) else [])) (live MI A) ->
    eff MI A0 A M0 M W F -> (forall a, F a -> p <= a < p + 32 \/ umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl2 bc2 ents2 a \/ (sp + 8 <= a < sp + 16)) ->
    (forall a, F a -> ~ in_ranges (ly_img L) a) ->
    srealizes SEGS (cfg fx1 R NT_EMPTY M model) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros fx1 p A M model R bl2 bc2 ents2 rh F CO FZ Hbc2 Hload Q22 Q10 Q11 Q27 Cb0 U2 PERM2 Hpa Hrf Hrt LAP EFF HF FOFF.
    destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
    pose proof (proj1 (nf_key _ _ _ _ _ _ _ _ _ NF)) as Hkr. cbn in Hkr.
    destruct CO as [AI MS Hfs Hfds SX B Q23 Q25 FR DEF8 DEFW Hp0 Hpc Hpal Hpl Hpnew Cnh Cnk DEFp].
    pose proof FR as FR'. destruct FR' as (_ & Fp1 & _). unfold cell8 in Fp1.
    assert (Hlen : Zlength ents2 = Zlength ents) by (unfold Zlength; rewrite (Permutation_length PERM2); reflexivity).
    pose proof (h_def (u_hdr U2)) as HDEF. pose proof (h_size (u_hdr U2)) as Csz. pose proof (h_p1 (u_hdr U2)) as Cp1. unfold cell8 in Cp1.
    pose proof (u_bl_lo U2 Hbc2) as Hbl0. pose proof (u_bl_hi U2) as Hbl1. pose proof (u_bl_obj U2 Hbc2) as Hblo. unfold apart in Hblo.
    pose proof (u_bseq U2) as HB2. pose proof (BSEQ_bound bc2 HB2) as Hbc2r.
    assert (Hch : 0 <= hmod key bc2 < bc2) by (unfold hmod; apply Z.mod_pos_bound; lia).
    set (ch := hmod key bc2) in *.
    assert (DEFbl : defined M bl2 (8 * bc2)).
    { destruct (u_blive U2) as [[? ?]|[_ Hin]]; [lia|]. destruct (live_facts' A M model bl2 (8 * bc2) AI Hin) as (_ & _ & _ & Hall).
      intros i Hi. exact (proj2 (Hall (bl2 + i) ltac:(lia))). }
    assert (Hblown : forall a, bl2 <= a < bl2 + 8 * bc2 -> ~ owned MI A a).
    { destruct (u_blive U2) as [[? ?]|[_ Hin]]; [lia|]. destruct (live_facts' A M model bl2 (8 * bc2) AI Hin) as (_ & _ & _ & Hall).
      intros a Ha. exact (proj1 (Hall a Ha)). }
    assert (Hblc : bl2 + 8 * bc2 <= alloc_ceiling).
    { destruct (u_blive U2) as [[? ?]|[_ Hin]]; [lia|]. destruct (live_facts' A M model bl2 (8 * bc2) AI Hin) as (_ & _ & Hc & _). exact Hc. }
    assert (Hpbl : apart p 32 bl2 (8 * bc2)).
    { apply Hpa. unfold umap_blocks. destruct (Z.eqb_spec bc2 0); [lia|]. apply in_app_iff. left. left. reflexivity. }
    assert (Hfoot_p : forall a, umap_foot 32 obj bl2 bc2 ents2 a -> ~ (p <= a < p + 32)).
    { intros a Ha Hpa'. destruct (umap_foot_hb 32 obj bl2 bc2 ents2 a Ha) as [Hh | ([q m] & Hq & Hqa)]; [lia|]. cbn in Hqa.
      pose proof (Hpa q m Hq) as Hap. unfold apart in Hap.
      assert (Hm : 0 < m).
      { unfold umap_blocks in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
        - destruct (Z.eqb_spec bc2 0); [destruct Hq|]. destruct Hq as [Hq|[]]. injection Hq as <- <-. lia.
        - apply in_map_iff in Hq. destruct Hq as (e & He & _). injection He as _ <-. lia. }
      lia. }
    pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs). unfold apart in Hpbl.

    assert (FIN : forall R5 (M5 : mem) (extra : option Z),

      (match extra with None => ents2 = [] | Some j => exists f kf vf rest, ents2 = (f, (kf, vf)) :: rest /\ j = hmod kf bc2 end) ->
      M5 = (match extra with
            | None => wbytes (wbytes (wbytes M (Z_to_bv 64 sent) (word_to_le_bytes 8 (Z_to_bv 64 p)))
                                    (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 (hdaddr ents2))))
                            (Z_to_bv 64 (bl2 + 8 * ch)) (word_to_le_bytes 8 (Z_to_bv 64 sent))
            | Some j => wbytes (wbytes (wbytes (wbytes M (Z_to_bv 64 sent) (word_to_le_bytes 8 (Z_to_bv 64 p)))
                                    (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 (hdaddr ents2))))
                            (Z_to_bv 64 (bl2 + 8 * ch)) (word_to_le_bytes 8 (Z_to_bv 64 sent)))
                            (Z_to_bv 64 (bl2 + 8 * j)) (word_to_le_bytes 8 (Z_to_bv 64 p))
            end) ->
      base_ok R5 -> getr R5 25%bv = Z_to_bv 64 p -> getr R5 27%bv = Z_to_bv 64 (t3c val) ->
      srealizes SEGS (cfg fx1 R5 NT_SIZE M5 model) K).
    { intros R5 M5 extra Hext HM5 B5 Q25' Q27'.

      assert (Hj : exists j, 0 <= j < bc2 /\ (match extra with None => j = ch | Some j' => j' = j end)
                   /\ (forall a : word, ~ (obj + 16 <= bv_unsigned a < obj + 24) -> ~ (p <= bv_unsigned a < p + 8) ->
                                        ~ (bl2 + 8 * ch <= bv_unsigned a < bl2 + 8 * ch + 8) -> ~ (bl2 + 8 * j <= bv_unsigned a < bl2 + 8 * j + 8) -> M5 a = M a)
                   /\ (forall a : word, M a <> None -> M5 a <> None)
                   /\ cell8 SEGS M5 (obj + 16) p /\ cell8 SEGS M5 p (hdaddr ents2)
                   /\ (j <> ch -> cell8 SEGS M5 (bl2 + 8 * ch) (obj + 16)) /\ (extra <> None -> cell8 SEGS M5 (bl2 + 8 * j) p) /\ (extra = None -> cell8 SEGS M5 (bl2 + 8 * ch) (obj + 16))
                   /\ (extra <> None -> exists f kf vf rest, ents2 = (f, (kf, vf)) :: rest /\ j = hmod kf bc2) /\ (extra = None -> ents2 = [])).
      { pose proof (proj1 Cp1) as Hhdr. unfold apart in Hpbl.
        destruct extra as [j|].
        - destruct Hext as (f & kf & vf & rest & HE2 & Hjk).
          assert (Hjr : 0 <= j < bc2) by (rewrite Hjk; unfold hmod; apply Z.mod_pos_bound; lia).
          exists j. split; [exact Hjr|]. split; [reflexivity|]. subst M5.
          split.
          { intros a H1 H2 H3 H4. pose proof (u64_range a).
            rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
          split; [intros a Ha; repeat apply wbytes_grows; exact Ha|].
          split; [unfold cell8; cellpeel|]. split; [unfold cell8; cellpeel|].
          split; [intros Hne; unfold cell8; cellpeel|]. split; [intros _; unfold cell8; cellpeel|]. split; [intros HX; discriminate HX|].
          split; [intros _; exists f, kf, vf, rest; split; assumption | intros HX; discriminate HX].
        - exists ch. split; [exact Hch|]. split; [reflexivity|]. subst M5.
          split.
          { intros a H1 H2 H3 H4. pose proof (u64_range a).
            rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
          split; [intros a Ha; repeat apply wbytes_grows; exact Ha|].
          split; [unfold cell8; cellpeel|]. split; [unfold cell8; cellpeel|].
          split; [intros Hne; exfalso; exact (Hne eq_refl)|]. split; [intros HX; exfalso; exact (HX eq_refl)|]. split; [intros _; unfold cell8; cellpeel|].
          split; [intros HX; exfalso; exact (HX eq_refl) | intros _; exact Hext]. }
      clear HM5 Hext.
      destruct Hj as (j & Hjr & Hjx & HM5w & HM5g & C5p1 & C5n & C5s & C5j & C5s' & HexS & HexN).
      assert (AI5 : ainv MI A M5 model).
      { eapply (ai_frame MI); [exact AI | | exact HM5g | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply HM5w; intros Hx.
        - exact (hi_unowned' A M model (bv_unsigned x) AI ltac:(lia) Ho).
        - destruct (live_facts' A M model p 32 AI Hpl) as (_ & _ & _ & Hall). exact (proj1 (Hall (bv_unsigned x) ltac:(lia)) Ho).
        - exact (Hblown (bv_unsigned x) ltac:(lia) Ho).
        - exact (Hblown (bv_unsigned x) ltac:(lia) Ho). }
      assert (FOFF5 : forall a, (obj + 16 <= a < obj + 24 \/ p <= a < p + 8 \/ bl2 <= a < bl2 + 8 * bc2) -> ~ in_ranges (ly_img L) a).
      { intros a [Ha | [Ha | Ha]] Hi.
        + pose proof (HLimg_lo _ Hi). lia.
        + exact (live_offimg' A M model p 32 a AI Hpl ltac:(lia) Hi).
        + destruct (u_blive U2) as [[? ?]|[_ Hin]]; [lia|]. exact (live_offimg' A M model bl2 (8 * bc2) a AI Hin Ha Hi). }
      assert (EF5 : eff MI A A M M5 W (fun a => obj + 16 <= a < obj + 24 \/ p <= a < p + 8 \/ bl2 <= a < bl2 + 8 * bc2)).
      { apply eff_store; [| exact HM5g]. intros x HFx _. apply HM5w; intros Hx; apply HFx; [left | right; left | right; right | right; right]; lia. }
      eapply (finish fx1 p A M5 model R5 bl2 bc2 ents2 ((p, (key, val)) :: ents2) rh
                (fun a => F a \/ obj + 16 <= a < obj + 24 \/ p <= a < p + 8 \/ bl2 <= a < bl2 + 8 * bc2)).
      - exact AI5. - exact MS. - exact Hfs. - exact Hfds.
      - eapply (sx_inv_via_eff' s A A M M5 model W _ SX AI EF5); [exact (own_sx_via_eff' A0 A M0 M W F EFF Hown_sx FOFF) | exact Herr_sx | exact FOFF5 | unfold Wnt; cbn; lia].
      - exact FZ.
      - exact B5. - exact Q25'. - exact Q27'.
      - eapply cellw_agree; [exact Csz | | lia | cbn; lia]. intros i Hi. apply HM5w; rewrite u64_of_Z by lia; lia.
      - intros i Hi. apply HM5g. apply HDEF. exact Hi.
      - pose proof (u_load U2). unfold Zlength in *. lia.
      - intros i Hi. apply HM5g. apply DEFp. exact Hi.
      - intros i Hi. apply HM5g. apply DEF8. exact Hi.
      - exact Hp0. - exact Hpc. - exact Hpl.
      -
        intros M' HM'w HM'g Csz' Hnv'.
        apply (umapx_link A M M' p bl2 bc2 val [] ents2 U2 Hbc2 ltac:(cbn [app]; lia) Hpl Hp0 Hpc Hpal Hpa).
        + eapply cellw_agree; [exact C5n | | lia | cbn; lia]. intros i Hi. apply HM'w; rewrite u64_of_Z by lia; lia.
        + eapply cellw_agree; [exact Cnh | | lia | cbn; lia]. intros i Hi. rewrite HM'w by (rewrite u64_of_Z by lia; lia). apply HM5w; rewrite u64_of_Z by lia; lia.
        + eapply cellw_agree; [exact Cnk | | lia | cbn; lia]. intros i Hi. rewrite HM'w by (rewrite u64_of_Z by lia; lia). apply HM5w; rewrite u64_of_Z by lia; lia.
        + exact Hnv'.
        + cbn [lasta map last]. eapply cellw_agree; [exact C5p1 | | lia | cbn; lia]. intros i Hi. apply HM'w; rewrite u64_of_Z by lia; lia.
        + cbn [app]. exact Csz'.
        + intros x Hx. apply HM'g, HM5g, Hx.
        + cbn [lasta map last app]. intros a Ha Hnb Hnsz Hnbl. pose proof (foot_low_or_high_gen C A M model bl2 bc2 _ a AI U2 Ha) as Har.
          pose proof (Hfoot_p a Ha). rewrite HM'w by (rewrite u64_of_Z by lia; lia). apply HM5w; rewrite u64_of_Z by lia; lia.
        +
          intros i Hi.
          assert (Cbi : forall b', (i <> ch -> i <> j -> cell8 SEGS M (bl2 + 8 * i) b') -> (i = ch -> i <> j -> b' = obj + 16) -> (i = j -> extra <> None -> b' = p) -> (i = ch -> extra = None -> b' = obj + 16) ->
                    cell8 SEGS M' (bl2 + 8 * i) b').
          { intros b' H1 H2 H3 H4.
            assert (C5 : cell8 SEGS M5 (bl2 + 8 * i) b').
            { destruct extra as [j'|].
              - destruct (Z.eq_dec i j) as [->|Hnj].
                + rewrite (H3 eq_refl ltac:(discriminate)). apply C5j. discriminate.
                + destruct (Z.eq_dec i ch) as [->|Hnc].
                  * rewrite (H2 eq_refl Hnj). apply C5s. intros HX. exact (Hnj (eq_sym HX)).
                  * eapply cellw_agree; [exact (H1 Hnc Hnj) | | lia | cbn; lia]. intros k Hk. apply HM5w; rewrite u64_of_Z by lia; lia.
              - subst j. destruct (Z.eq_dec i ch) as [->|Hnc].
                + rewrite (H4 eq_refl eq_refl). apply C5s'. reflexivity.
                + eapply cellw_agree; [exact (H1 Hnc Hnc) | | lia | cbn; lia]. intros k Hk. apply HM5w; rewrite u64_of_Z by lia; lia. }
            eapply cellw_agree; [exact C5 | | lia | cbn; lia]. intros k Hk. apply HM'w; rewrite u64_of_Z by lia; lia. }
          destruct (Z.eq_dec i j) as [Hij|Hnj]; [destruct extra as [j'|] eqn:HX|].
          *
            exists p. split; [apply Cbi; intros; first [congruence | reflexivity]|]. right. left. left. reflexivity.
          *
            exists (obj + 16). split; [apply Cbi; intros; first [congruence | reflexivity]|].
            right. right. split; [reflexivity|]. split; [discriminate|]. cbn [app hdkey fst snd]. lia.
          * destruct (Z.eq_dec i ch) as [Hic|Hnc].
            -- exists (obj + 16). split; [apply Cbi; intros; first [congruence | reflexivity]|].
               right. right. split; [reflexivity|]. split; [discriminate|]. cbn [app hdkey fst snd]. exact Hic.
            -- destruct (u_bkt U2 i Hi) as (b'' & Cb'' & Hok''). exists b''. split; [apply Cbi; intros; first [congruence | exact Cb'']|].
               destruct Hok'' as [H0 | [Hn | (Hs & Hne & Hi')]]; [left; exact H0 | right; left; right; exact Hn | exfalso].
               destruct extra as [j'|]; [| exact (Hne (HexN eq_refl))].
               destruct (HexS ltac:(discriminate)) as (f & kf & vf & rest & HE2 & Hjk). rewrite HE2 in Hi'. cbn [hdkey fst snd] in Hi'.
               apply Hnj. rewrite Hi', Hjk. reflexivity.
      - left. reflexivity.
      - apply perm_skip. exact PERM2.
      - exact Hrf. - exact Hrt. - exact LAP.
      - eapply eff_trans; [exact EFF | exact EF5 | intros a Ha; eapply hi_unowned'; [exact AI5 | unfold W_of, Wnt in Ha; cbn in Ha; lia]].
      - intros a [Ha | [Ha | [Ha | Ha]]].
        + destruct (HF a Ha) as [H|[H|[H|H]]]; [right; left; right; right; exists p; split; [left; reflexivity | lia] | left; exact H | right; left; exact (umap_foot_mono _ _ [] _ _ _ H) | right; right; exact H].
        + right. left. left. lia.
        + right. left. right. right. exists p. split; [left; reflexivity | lia].
        + right. left. right. left. split; [exact Hbc2 | exact Ha].
      - intros a [Ha | Ha]; [exact (FOFF a Ha) | exact (FOFF5 a Ha)]. }

    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 bc2; Z_to_bv 64 key; Z_to_bv 64 bl2; Z_to_bv 64 (bl2 + 8 * ch); Z_to_bv 64 (t3c val);
                        Z_to_bv 64 sent; Z_to_bv 64 (hdaddr ents2); Z_to_bv 64 (hdkey ents2)]).
    assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (22%bv, EVar 35); (23%bv, EVar 36); (10%bv, EVar 37); (11%bv, EVar 38); (27%bv, EVar 39)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (DEF24 : defined M (sp + 24) 8) by (exact (cellw_high_defined M (sp + 24) 8 _ (proj1 (proj2 FR)) ltac:(lia) ltac:(cbn; lia))).
    assert (Hdummy : bl2 = bl2) by reflexivity.
    clear - HR HK FIN B MS DEFp HDEF DEFbl DEF24 Fp1 Hkr Hbc2r Hbc2 Hch Hbl0 Hbl1 Hblo Hobjlo Hobjhi Hs1 Hsplo Hn16 Hsphi Hp0 Hpc Hcl Hcv Cp1 U2 Hpa Hpbl HB2 Hdummy.
    destruct ents2 as [|[f [kf vf]] rest] eqn:HE2.
    - cbn [hdaddr hdkey] in *.
      xruns HR HK 100%nat STOPSF (SCR [true] [EVar 40; EVar 41] []) 50%N; [scE Hdummy Hdummy DEFp HDEF DEFbl|].
      fin5 FIN HR' (@None Z) ltac:(reflexivity) Hdummy B.
    - cbn [hdaddr hdkey] in *.
      destruct (u_node U2 f kf vf (or_introl eq_refl)) as (Hflv & Hf0 & Hf1 & _ & Cfh & _ & Hkf & _).
      unfold cell8 in Cfh.
      assert (Hpf : apart p 32 f 32).
      { apply Hpa. unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (f, (kf, vf)). split; [reflexivity | left; reflexivity]. }
      assert (Hhf : 0 <= hmod kf bc2 < bc2) by (unfold hmod; apply Z.mod_pos_bound; lia).
      assert (Hlandr : 0 <= Z.land bc2 (bc2 - 1) <= 2 * bc2).
      { pose proof (Z.add_lor_land bc2 (bc2 - 1)). pose proof (Z.land_nonneg bc2 (bc2 - 1)). pose proof (Z.lor_nonneg bc2 (bc2 - 1)). lia. }
      assert (HK2 : know_ok SEGS E M [KDisj (SA (EVar 41) 0) (ELit 32) (SA (EVar 40) 0) (ELit 8);
                                     KDisj (SA (EVar 41) 0) (ELit 32) (SA (EVar 32) 0) (ELit 32);
                                     KDisj (SA (EVar 41) 0) (ELit 32) (SA (EVar 38) 0) (ELit 8)]).
      { destruct (u_node U2 f kf vf (or_introl eq_refl)) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfo & Hfb). unfold apart in Hfo. pose proof (Hfb Hbc2) as Hfb'. unfold apart in Hfb'.
        repeat apply Forall_cons; try apply Forall_nil.
        - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia].
        - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | unfold apart in Hpf; lia].
        - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia]. }
      clear HK.
      destruct (bseq_pow2 bc2 HB2 Hbc2) as [[Hbc22 Hland] | [Hbc23 Hland]].
      +
        assert (Hj : bl2 + 8 * Z.land kf (bc2 - 1) = bl2 + 8 * hmod kf bc2) by (rewrite Hbc22; change (2 - 1) with 1; rewrite land_1; reflexivity).
        xruns HR HK2 100%nat STOPSF (SCR [false; false] [EVar 40; EVar 41; EVar 42] []) 50%N; [scE Hland Hj DEFp HDEF DEFbl|].
        fin5 FIN HR' (Some (hmod kf bc2)) ltac:(exists f, kf, vf, rest; split; reflexivity) Hj B.
      + destruct (Z.lt_ge_cases kf bc2) as [Hlt | Hge].
        * assert (Hj : bl2 + 8 * kf = bl2 + 8 * hmod kf bc2) by (unfold hmod; rewrite Z.mod_small by lia; reflexivity).
          xruns HR HK2 100%nat STOPSF (SCR [false; true; true] [EVar 40; EVar 41; EVar 42] []) 50%N; [scE Hland Hj DEFp HDEF DEFbl|].
          fin5 FIN HR' (Some (hmod kf bc2)) ltac:(exists f, kf, vf, rest; split; reflexivity) Hj B.
        * pose proof Hhf as Hhf'. unfold hmod in Hhf'.
          xruns HR HK2 100%nat STOPSF (SCR [false; true; false] [EVar 40; EVar 41; EVar 42] []) 50%N; [scE Hland Hdummy DEFp HDEF DEFbl|].
          fin5 FIN HR' (Some (hmod kf bc2)) ltac:(exists f, kf, vf, rest; split; reflexivity) Hdummy B.
  Qed.

  Lemma phaseF : forall (fx1 : FPState) p A M model R (bl2 bc2 : Z) (ents2 : list ent) (rh : bool) (F : Z -> Prop),
    core p A M model R -> frm_zero (@fp_csr fx1) -> bc2 <> 0 -> Zlength ents + 1 <= bc2 ->
    getr R 22%bv = Z_to_bv 64 bc2 -> getr R 26%bv = Z_to_bv 64 (hmod key bc2) -> getr R 27%bv = Z_to_bv 64 (t3c val) ->
    umapx MI 32 (nval32 SEGS) A M obj bl2 bc2 ents2 -> Permutation ents2 ents ->
    (forall q m, In (q, m) (umap_blocks 32 bl2 bc2 ents2) -> apart p 32 q m) ->
    (rh = false -> bl2 = bl /\ bc2 = bc) -> (rh = true -> (bc = 0 \/ Zlength ents = bc) /\ bc2 = bseq_next bc) ->
    lapply (live MI A0) (LAdd p 32 :: (if rh then LAdd bl2 (8 * bc2) :: (if bc =? 0 then [] else [LDel bl]) else [])) (live MI A) ->
    eff MI A0 A M0 M W F -> (forall a, F a -> p <= a < p + 32 \/ umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl2 bc2 ents2 a \/ (sp + 8 <= a < sp + 16)) ->
    (forall a, F a -> ~ in_ranges (ly_img L) a) ->
    srealizes SEGS (cfg fx1 R NT_INS M model) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros fx1 p A M model R bl2 bc2 ents2 rh F CO FZ Hbc2 Hload Q22 Q26 Q27 U2 PERM2 Hpa Hrf Hrt LAP EFF HF FOFF.
    destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
    pose proof (proj1 (nf_key _ _ _ _ _ _ _ _ _ NF)) as Hkr. cbn in Hkr.
    pose proof CO as CO'. destruct CO' as [AI MS Hfs Hfds SX B Q23 Q25 FR DEF8 DEFW Hp0 Hpc Hpal Hpl Hpnew Cnh Cnk DEFp].
    pose proof (u_bseq U2) as HB2. pose proof (BSEQ_bound bc2 HB2) as Hbc2r.
    assert (Hhm : 0 <= hmod key bc2 < bc2) by (unfold hmod; apply Z.mod_pos_bound; lia).
    destruct (u_bkt U2 (hmod key bc2) Hhm) as (b & Cb & Hbok). pose proof Cb as Cb'. unfold cell8 in Cb'. pose proof (proj1 Cb') as Hbr.
    pose proof (u_bl_lo U2 Hbc2) as Hbl0. pose proof (u_bl_hi U2) as Hbl1. pose proof (h_bl (u_hdr U2)) as Cbl2. unfold cell8 in Cbl2.
    pose proof (h_def (u_hdr U2)) as HDEF.
    assert (COR : forall Rx, base_ok Rx -> getr Rx 23%bv = Z_to_bv 64 key -> getr Rx 25%bv = Z_to_bv 64 p -> core p A M model Rx).
    { intros Rx HB Q23' Q25'. constructor;
        [ exact AI | exact MS | exact Hfs | exact Hfds | exact SX | exact HB | exact Q23' | exact Q25' | exact FR | exact DEF8 | exact DEFW
        | exact Hp0 | exact Hpc | exact Hpal | exact Hpl | exact Hpnew | exact Cnh | exact Cnk | exact DEFp ]. }
    pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 bc2; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc2); Z_to_bv 64 (t3c val); Z_to_bv 64 bl2; Z_to_bv 64 b]).
    assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (22%bv, EVar 35); (23%bv, EVar 36); (26%bv, EVar 37); (27%bv, EVar 38)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (Hdummy : bl2 = bl2) by reflexivity.
    destruct (Z.eq_dec b 0) as [Hbz | Hbnz].
    - xruns HR HK 100%nat STOPSF (SCR [true] [EVar 39; EVar 40] []) 50%N; [scE Hdummy Hdummy DEFp HDEF DEFp|].
      eapply (phaseF_empty fx1 p A M model R' bl2 bc2 ents2 rh F);
        [ apply COR; [nt_base_from HR' B | let Q := fresh in rreg HR' 23%bv Q; exact Q | let Q := fresh in rreg HR' 25%bv Q; exact Q]
        | exact FZ | exact Hbc2 | exact Hload
        | let Q := fresh in rreg HR' 22%bv Q; exact Q
        | let Q := fresh in rreg HR' 10%bv Q; exact Q
        | let Q := fresh in rreg HR' 11%bv Q; rewrite Q; rewrite ?w_mul, ?w_add by lia; f_equal; lia
        | let Q := fresh in rreg HR' 27%bv Q; exact Q
        | rewrite <- Hbz; exact Cb | exact U2 | exact PERM2 | exact Hpa | exact Hrf | exact Hrt | exact LAP | exact EFF | exact HF | exact FOFF ].
    - xruns HR HK 100%nat STOPSF (SCR [false] [EVar 39; EVar 40] []) 50%N; [scE Hdummy Hdummy DEFp HDEF DEFp|].
      eapply (phaseF_pn fx1 p A M model R' bl2 bc2 ents2 rh b F);
        [ apply COR; [nt_base_from HR' B | let Q := fresh in rreg HR' 23%bv Q; exact Q | let Q := fresh in rreg HR' 25%bv Q; exact Q]
        | exact FZ | exact Hbc2 | exact Hload
        | let Q := fresh in rreg HR' 22%bv Q; exact Q
        | let Q := fresh in rreg HR' 12%bv Q; exact Q
        | let Q := fresh in rreg HR' 27%bv Q; exact Q
        | exact Hbok | exact Hbnz | exact U2 | exact PERM2 | exact Hpa | exact Hrf | exact Hrt | exact LAP | exact EFF | exact HF | exact FOFF ].
  Qed.

End NtF.

Arguments finish {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C fx1 p A M model R bl2 bc2 ents2 ents' rh F.
Arguments phaseF {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C fx1 p A M model R bl2 bc2 ents2 rh F.
End HNtF.

Module HNtR.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFind OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtCtx OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtA OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.S1_code_67e94_68324.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition STOPSR : list Z := [NT_FDIV; NT_FCVTLU; NT_NP; NT_NPR; NT_NEWE].

#[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

Section NtR.
Context {AC : AllocCeiling}.

  Variables (L : Layout) (MI : MallocIface SEGS L) (ST : StaticsIface SEGS L) (NEW_STACK DEL_STACK : Z).
  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp parser key bl bc : Z) (val : Z * Z * Z) (v2 : Z) (ents : list (Z * (Z * (Z * Z * Z)))) (K : TSet).
  Variable C : @ntctx AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K.
  #[local] Abbreviation NTS := (NT_STACK NEW_STACK DEL_STACK).
  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI (c_HLimg_lo C) (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST (c_HLimg_lo C) (c_HLrw_img C) (c_HLrelro_img C) (c_HLrw_relro C) (c_HLerr_rw C)).
  #[local] Abbreviation ro_clear_via_eff' := (ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation agree_block_via_eff' := (agree_block_via_eff L MI (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation own_sx_via_eff' := (own_sx_via_eff L MI ST (c_HLrw_img C)).
  #[local] Abbreviation hi_unowned' := (hi_unowned L MI (c_HLimg_lo C) (c_HLrw_img C)).
  #[local] Abbreviation obj := (parser + 136).
  #[local] Abbreviation sent := (parser + 152).
  #[local] Abbreviation W := (Wnt NEW_STACK DEL_STACK sp).
  #[local] Abbreviation base_ok := (nt_base_ok L R0 sp parser val v2).
  #[local] Abbreviation pframe := (nt_pframe sp parser key).
  #[local] Abbreviation SPF := (sp_facts C).
  #[local] Abbreviation BCF := (bc_facts C).
  #[local] Ltac ctx := ntctx_pose C.

  #[local] Abbreviation core := (@HNtA.core AC L MI ST NEW_STACK DEL_STACK A0 s R0 model0 sp parser key val v2).

  Record rcall (p : Z) (A : AS MI) (M : mem) (model : Model) (R : bvmap 5 word) : Prop := RCALL {
    rc_ai : ainv MI A M model;
    rc_ms : mstd model;
    rc_fs : m_fs model = m_fs model0;
    rc_fds : m_fds model = m_fds model0;
    rc_sx : sx_inv ST s M;
    rc_regs : base_ok R;
    rc_s7 : getr R 23%bv = Z_to_bv 64 key;
    rc_s9 : getr R 25%bv = Z_to_bv 64 p;
    rc_s10 : getr R 26%bv = Z_to_bv 64 (bseq_next bc);
    rc_s6 : getr R 22%bv = Z_to_bv 64 (8 * bseq_next bc);
    rc_a0 : getr R 10%bv = Z_to_bv 64 (8 * bseq_next bc);
    rc_ra : getr R 1%bv = Z_to_bv 64 NT_NEW2R;
    rc_frame : pframe M;
    rc_def8 : defined M (sp + 8) 8;
    rc_defw : defined M (sp - NTS) NTS;
    rc_spill : cell8 SEGS M (sp + 8) (t3c val);
    rc_p0 : 0 < p; rc_pc : p + 32 <= alloc_ceiling; rc_pal : p mod 16 = 0;
    rc_plive : In (p, 32) (live MI A);
    rc_pnew : ~ In p (map fst (live MI A0));
    rc_nh : cell8 SEGS M (p + 8) key;
    rc_nk : cell4 SEGS M (p + 16) key;
    rc_pdef : defined M p 32;
    rc_eff : eff MI A0 A M0 M W (fun a => p <= a < p + 32 \/ sp + 8 <= a < sp + 16);
    rc_ladd : live_add p 32 (live MI A0) (live MI A);
    rc_U : umapx MI 32 (nval32 SEGS) A M obj bl bc ents;
    rc_grow : bc = 0 \/ Zlength ents = bc;
    rc_roc : ro_clear L M
  }.

  Lemma phaseR1 : forall (fx1 : FPState) p A M model R,
    core p A M model R -> getr R 22%bv = Z_to_bv 64 bc -> getr R 27%bv = Z_to_bv 64 (t3c val) ->
    frm_zero (@fp_csr fx1) -> fholds fx1 14%bv (ieee (Zlength ents + 1)) -> fholds fx1 15%bv one32 ->
    (bc = 0 \/ Zlength ents = bc) ->
    eff MI A0 A M0 M W (fun a => p <= a < p + 32) -> live_add p 32 (live MI A0) (live MI A) ->
    umapx MI 32 (nval32 SEGS) A M obj bl bc ents -> ro_clear L M ->
    (forall (fx2 : FPState) M' R', frm_zero (@fp_csr fx2) -> rcall p A M' model R' -> srealizes SEGS (cfg fx2 R' NT_NEWE M' model) K) ->
    srealizes SEGS (cfg fx1 R NT_GROW M model) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros fx1 p A M model R CO Q22 Q27 FZ Hf14 Hf15 Hgrow EFF LADD U RC POST.
    destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
    destruct BCF as (HbB & Hbcr & Hload & Hsz0).
    destruct CO as [AI MS Hfs Hfds SX B Q23 Q25 FR DEF8 DEFW Hp0 Hpc Hpal Hpl Hpnew Cnh Cnk DEFp].
    pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
    pose proof (ieee_range (Zlength ents + 1) ltac:(lia)) as Hie1.
    destruct (bseq_next_facts bc HbB Hlast) as (HnB & Hbcn & Hn28 & _).
    pose proof (h_bc (u_hdr U)) as Cbc. unfold cell8 in Cbc.
    destruct (live_facts' A M model p 32 AI Hpl) as (_ & _ & _ & Hpall).
    destruct ASP8 as (_ & _ & Ho8).

    set (M1 := wbytes M (Z_to_bv 64 (sp + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (t3c val)))).
    assert (HM1w : forall a : word, ~ (sp + 8 <= bv_unsigned a < sp + 16) -> M1 a = M a).
    { intros a Ha. pose proof (u64_range a). unfold M1.
      rewrite wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
    assert (HM1g : forall a : word, M a <> None -> M1 a <> None) by (intros a Ha; unfold M1; apply wbytes_grows; exact Ha).
    assert (AI1 : ainv MI A M1 model).
    { eapply (ai_frame MI); [exact AI | | exact HM1g | reflexivity | reflexivity].
      intros x Ho. pose proof (u64_range x). apply HM1w; intros Hx. exact (hi_unowned' A M model (bv_unsigned x) AI ltac:(lia) Ho). }
    assert (EFF1 : eff MI A0 A M0 M1 W (fun a => p <= a < p + 32 \/ sp + 8 <= a < sp + 16)).
    { eapply eff_weaken; [eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned'; [exact AI1 | unfold W_of, Wnt in Ha; cbn in Ha; lia]]|].
      - eapply eff_store with (F := fun a : Z => sp + 8 <= a < sp + 16); [| exact HM1g]. intros x HF _. apply HM1w. exact HF.
      - intros a Ha. exact Ha. }
    assert (HM1a : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> (a + k <= sp + 8 \/ sp + 16 <= a) -> agree_on M M1 a k).
    { intros a k Ha Hak H1 i Hi. apply HM1w. rewrite u64_of_Z by lia. lia. }

    assert (FIN : forall (fx2 : FPState) R' M', frm_zero (@fp_csr fx2) ->
              base_ok R' -> getr R' 23%bv = Z_to_bv 64 key -> getr R' 25%bv = Z_to_bv 64 p -> getr R' 26%bv = Z_to_bv 64 (bseq_next bc) ->
              getr R' 22%bv = Z_to_bv 64 (8 * bseq_next bc) -> getr R' 10%bv = Z_to_bv 64 (8 * bseq_next bc) -> getr R' 1%bv = Z_to_bv 64 NT_NEW2R ->
              (M' = M1 \/ M' = wbytes M1 (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 NT_NPR))) ->
              srealizes SEGS (cfg fx2 R' NT_NEWE M' model) K).
    { intros fx2 R' M' FZ2 B' Q23' Q25' Q26' Q22' Q10' Q1' HM'.
      assert (HMw : forall a : word, ~ (sp - 8 <= bv_unsigned a < sp) -> M' a = M1 a).
      { intros a Ha. destruct HM' as [-> | ->]; [reflexivity|]. pose proof (u64_range a).
        rewrite wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
      assert (HMg : forall a : word, M1 a <> None -> M' a <> None) by (intros a Ha; destruct HM' as [-> | ->]; [exact Ha | apply wbytes_grows; exact Ha]).
      assert (HMa : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> (a + k <= sp - 8 \/ sp <= a) -> agree_on M1 M' a k).
      { intros a k Ha Hak H1 i Hi. apply HMw. rewrite u64_of_Z by lia. lia. }
      assert (AI' : ainv MI A M' model).
      { eapply (ai_frame MI); [exact AI1 | | exact HMg | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply HMw; intros Hx. exact (hi_unowned' A M1 model (bv_unsigned x) AI1 ltac:(lia) Ho). }
      assert (EFF' : eff MI A0 A M0 M' W (fun a => p <= a < p + 32 \/ sp + 8 <= a < sp + 16)).
      { eapply eff_weaken; [eapply eff_trans; [exact EFF1 | | intros a Ha; eapply hi_unowned'; [exact AI' | unfold W_of, Wnt in Ha; cbn in Ha; lia]] |].
        + eapply eff_store with (F := fun _ : Z => False); [| exact HMg]. intros x _ HW. apply HMw. intros Hx. apply HW. unfold W_of, Wnt. cbn. lia.
        + intros a [Ha|[]]. exact Ha. }
      assert (FOFF' : forall a, (p <= a < p + 32 \/ sp + 8 <= a < sp + 16) -> ~ in_ranges (ly_img L) a).
      { intros a [Ha | Ha] Hi; [exact (live_offimg' A M model p 32 a AI Hpl Ha Hi) | pose proof (HLimg_lo _ Hi); lia]. }
      apply (POST fx2 M' R' FZ2). constructor;
        [ exact AI' | exact MS | exact Hfs | exact Hfds | | exact B' | exact Q23' | exact Q25' | exact Q26' | exact Q22' | exact Q10' | exact Q1'
        | | | | | exact Hp0 | exact Hpc | exact Hpal | exact Hpl | exact Hpnew | | | | exact EFF' | exact LADD | | exact Hgrow | ].
      - eapply (sx_inv_via_eff' s A0 A M0 M' model0 W _ SX0 AI0 EFF' Hown_sx Herr_sx FOFF'). unfold Wnt; cbn; lia.
      - destruct FR as (F1 & F2 & F3 & F4 & F5 & F6). unfold nt_pframe.
        split; [|split; [|split; [|split; [|split]]]]; (eapply cellw_agree; [| eapply (agree_on_trans M M1 M'); [apply HM1a; cbn; lia | apply HMa; cbn; lia] | lia | cbn; lia]); eassumption.
      - intros i Hi. apply HMg. apply HM1g. apply DEF8. exact Hi.
      - intros i Hi. apply HMg. apply HM1g. apply DEFW. exact Hi.
      - eapply cellw_agree; [| apply HMa; cbn; lia | lia | cbn; lia]. unfold M1, cell8. cellpeel.
      - eapply cellw_agree; [exact Cnh | eapply (agree_on_trans M M1 M'); [apply HM1a; cbn; lia | apply HMa; cbn; lia] | lia | cbn; lia].
      - eapply cellw_agree; [exact Cnk | eapply (agree_on_trans M M1 M'); [apply HM1a; cbn; lia | apply HMa; cbn; lia] | lia | cbn; lia].
      - intros i Hi. apply HMg. apply HM1g. apply DEFp. exact Hi.
      - eapply (umapx_agree SEGS L MI 32 _ (nval32 SEGS) (nval32_agree SEGS) ltac:(lia) A A M M'); [exact U | | intros; assumption].
        intros a Ha. pose proof (foot_low_or_high_gen C A M model bl bc ents a AI U Ha).
        assert (Hno : ~ (obj <= a < obj + 40) -> a + 1 <= alloc_ceiling).
        { intros Hn. destruct (umap_foot_hb 32 obj bl bc ents a Ha) as [Hh | ([q m] & Hq & Hqa)]; [exfalso; exact (Hn Hh)|]. cbn in Hqa.
          assert (Hql : In (q, m) (live MI A)).
          { rewrite (proj1 LADD). right. unfold umap_blocks in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
            - destruct (Z.eqb_spec bc 0); [destruct Hq|]. destruct Hq as [Hq|[]]. injection Hq as <- <-. destruct (u_blive U0) as [[? ?]|[_ Hin]]; [lia | exact Hin].
            - apply in_map_iff in Hq. destruct Hq as ([q' [k' v']] & Hq' & Hin). cbn in Hq'. injection Hq' as <- <-. exact (proj1 (u_node U0 q' k' v' Hin)). }
          destruct (live_facts' A M model q m AI Hql) as (_ & _ & Hqc & _). lia. }
        destruct ASPT as (Hs1' & _ & _).
        rewrite HMw by (rewrite u64_of_Z by lia; lia). apply HM1w. rewrite u64_of_Z by lia. lia.
      - eapply (ro_clear_frame L (fun a => sp - 8 <= a < sp + 16) M M').
        + exact RC.
        + intros x Hn. rewrite HMw by lia. apply HM1w. lia.
        + intros a Hro Ha. pose proof (HLimg_lo _ (proj1 Hro)). lia. }

    assert (NPK : forall (fx2 : FPState) Rn, bc <> 0 -> frm_zero (@fp_csr fx2) ->
              base_ok Rn -> getr Rn 23%bv = Z_to_bv 64 key -> getr Rn 25%bv = Z_to_bv 64 p ->
              getr Rn 10%bv = Z_to_bv 64 (np_arg bc) -> getr Rn 1%bv = Z_to_bv 64 NT_NPR ->
              srealizes SEGS (cfg fx2 Rn NT_NP M1 model) K).
    { intros fx2 Rn Hbc1 FZ2 Bn Q23' Q25' Q10' Q1'. pose proof Bn as Bn'. destruct Bn' as (Bn2 & Bn3 & Bn4 & Bn8 & Bn24 & Bn21 & Bn18 & Bns).
      assert (RC1 : ro_clear L M1).
      { eapply (ro_clear_frame L (fun a => sp + 8 <= a < sp + 16) M M1 RC); [intros x Hn; apply HM1w; exact Hn|]. intros a Hro Ha. pose proof (HLimg_lo _ (proj1 Hro)). lia. }
      destruct (NP fx2 Rn M1 bc sp (Z_to_bv 64 NT_NPR) HbB Hbc1 Hlast Q10' Q1' ltac:(apply bv_eq; vm_compute; reflexivity) Bn2
                   Hsp16' ltac:(lia) ltac:(lia)
                   ltac:(apply stack_room_of_defined; [lia | lia | lia |]; eapply defined_sub; [intros i Hi; apply HM1g; apply DEFW; exact Hi | lia | lia]) RC1)
        as (Rn' & Hms & KEPT & Qa0).
      eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | exact Hms |].
      zpc NT_NPR.
      set (Mn := wbytes M1 _ _).
      assert (Cbc' : cellw SEGS Mn (parser + 144) 8 bc).
      { replace (parser + 144) with (obj + 8) by lia. eapply cellw_agree; [exact Cbc | | lia | cbn; lia]. intros i Hi. unfold Mn. pose proof (u64_range (Z_to_bv 64 (obj + 8 + i))).
        rewrite wbytes_outside; [apply HM1w; rewrite u64_of_Z by lia; lia| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
      pose (E := Eseed Rn' [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 key; Z_to_bv 64 (bseq_next bc); Z_to_bv 64 bc]).
      assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (23%bv, EVar 35); (10%bv, EVar 36)]) Rn').
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; rewrite ?KEPT by inl; assumption. }
      assert (HK : know_ok SEGS E Mn []) by constructor.
      assert (BnK : base_ok Rn').
      { unfold nt_base_ok. rewrite !KEPT by inl. split; [exact Bn2|]. split; [exact Bn3|]. split; [exact Bn4|]. split; [exact Bn8|]. split; [exact Bn24|]. split; [exact Bn21|]. split; [exact Bn18|].
        intros r Hr. rewrite KEPT; [apply Bns; exact Hr|]. clear - Hr. cbn in Hr. unfold callee_saved. cbn. intuition congruence. }
      xruns HR HK 100%nat STOPSR (SCR [false; false] [EVar 37] []) 50%N.
      { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_srl by lia. rewrite (Z.div_small (bseq_next bc) (2 ^ 61)) by lia. rewrite br_ne by lia. bool_lia. }
      eapply (FIN fx2 R' Mn FZ2); [ nt_base_from HR' BnK | let Q := fresh in rreg HR' 23%bv Q; exact Q | let Q := fresh in rreg HR' 25%bv Q; exact Q
                                   | let Q := fresh in rreg HR' 26%bv Q; exact Q
                                   | let Q := fresh in rreg HR' 22%bv Q; rewrite Q; rewrite ?w_mul, ?w_sll by lia; f_equal; lia
                                   | let Q := fresh in rreg HR' 10%bv Q; rewrite Q; rewrite ?w_mul, ?w_sll by lia; f_equal; lia
                                   | let Q := fresh in rreg HR' 1%bv Q; exact Q | right; reflexivity ]. }

    Ltac scR DEF8 Hland :=
      split_scs;
      lazymatch goal with
      | |- sc_denot _ _ _ (SCStoreOk _ _) => sc_so; eapply (defined_sub _ _ _ _ _ DEF8); lia
      | |- sc_denot _ _ _ (SCFlat _ _) => sc_fl
      | |- sc_denot _ _ _ (SCBr _ _ _ _) =>
          cbn [sc_denot]; evs; nadd; repeat match goal with |- context [?x + -1] => change (x + -1) with (x - 1) end;
          rewrite ?w_and by lia; rewrite ?Hland; rewrite ?br_eq, ?br_ne, ?br_geu, ?br_ltu by lia; bool_lia
      | |- _ => sc_auto1
      end.

    assert (R1BC : forall (fxb : FPState) Rb (v10 : Z),
      frm_zero (@fp_csr fxb) -> fholds fxb 15%bv (ieee (Zlength ents + 1)) ->
      base_ok Rb -> getr Rb 22%bv = Z_to_bv 64 bc -> getr Rb 23%bv = Z_to_bv 64 key -> getr Rb 25%bv = Z_to_bv 64 p -> getr Rb 27%bv = Z_to_bv 64 (t3c val) ->
      getr Rb 10%bv = Z_to_bv 64 v10 -> getr Rb 11%bv = Z_to_bv 64 (2 * bc) ->
      ((bc = 0 /\ v10 = 1) \/ (bc <> 0 /\ v10 = 1 /\ Z.land (Z.max (2 * bc + 1) (Zlength ents + 1)) (Z.max (2 * bc + 1) (Zlength ents + 1) - 1) <> 0
                                /\ np_arg bc = Z.max (2 * bc + 1) (Zlength ents + 1))) ->
      srealizes SEGS (cfg fxb Rb 0x68048 M model) K).
    { intros fxb Rb v10 FZb Hg15 Bb Qb22 Qb23 Qb25 Qb27 Qb10 Qb11 Hcase.
      pose proof Bb as Bb'. destruct Bb' as (Bb2 & Bb3 & Bb4 & Bb8 & Bb24 & Bb21 & Bb18 & Bbs).
      assert (Hv10 : v10 = 1) by (destruct Hcase as [[_ H]|[_ [H _]]]; exact H).

      pose (E := Eseed Rb [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (t3c val); Z_to_bv 64 v10; Z_to_bv 64 (2 * bc)]).
      assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (22%bv, EVar 35); (23%bv, EVar 36); (27%bv, EVar 37); (10%bv, EVar 38); (11%bv, EVar 39)]) Rb).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.
      xruns HR HK 100%nat STOPSR (SCR [] [] []) 50%N; [split_scs; try sc_auto1|].
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
      rreg HRc 26%bv Qc26'.
      assert (Qc26 : getr Rc 26%bv = Z_to_bv 64 (2 * bc + 1)).
      { rewrite Qc26'. rewrite w_or by lia. rewrite Hv10, lor_2b by lia. reflexivity. }
      clear Qc26'. rreg HRc 8%bv Qx8. rreg HRc 2%bv Qx2. rreg HRc 22%bv Qx22. rreg HRc 23%bv Qx23. rreg HRc 25%bv Qx25. rreg HRc 27%bv Qx27. rreg HRc 10%bv Qc10.
      assert (Bc : base_ok Rc) by (nt_base_from HRc Bb). clear HRc HR HK.

      fp_fcvt_lu_s MS F_6800c D_6800c FZb Hg15 (Zlength ents + 1) 0x68050.
      set (Rd := regupd Rc 10%bv _).
      assert (Qd : forall r, r <> 10%bv -> getr Rd r = getr Rc r) by (intros r Hr; unfold Rd; apply getr_other; exact Hr).
      assert (Qd10 : getr Rd 10%bv = Z_to_bv 64 (Zlength ents + 1)) by (unfold Rd; apply getr_same; intros X; discriminate X).
      pose proof (Qd 8%bv ltac:(intros X; discriminate X)) as Qd8. rewrite Qx8 in Qd8.
      pose proof (Qd 2%bv ltac:(intros X; discriminate X)) as Qd2. rewrite Qx2 in Qd2.
      pose proof (Qd 22%bv ltac:(intros X; discriminate X)) as Qd22. rewrite Qx22 in Qd22.
      pose proof (Qd 23%bv ltac:(intros X; discriminate X)) as Qd23. rewrite Qx23 in Qd23.
      pose proof (Qd 25%bv ltac:(intros X; discriminate X)) as Qd25. rewrite Qx25 in Qd25.
      pose proof (Qd 27%bv ltac:(intros X; discriminate X)) as Qd27. rewrite Qx27 in Qd27.
      pose proof (Qd 26%bv ltac:(intros X; discriminate X)) as Qd26. rewrite Qc26 in Qd26.
      assert (Bd : base_ok Rd).
      { unfold nt_base_ok. rewrite !Qd by (intros X; discriminate X). destruct Bc as (? & ? & ? & ? & ? & ? & ? & Bcs).
        split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        intros r Hr. rewrite Qd; [apply Bcs; exact Hr|]. clear - Hr. cbn in Hr. intros ->. intuition discriminate. }

      pose (E := Eseed Rd [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (t3c val); Z_to_bv 64 (Zlength ents + 1); Z_to_bv 64 (2 * bc + 1); Z_to_bv 64 1]).
      assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (22%bv, EVar 35); (23%bv, EVar 36); (27%bv, EVar 37); (10%bv, EVar 38); (26%bv, EVar 39); (24%bv, EVar 40)]) Rd).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; try assumption.
        destruct Bd as (_ & _ & _ & _ & Bd24 & _). exact Bd24. }
      assert (HK : know_ok SEGS E M []) by constructor.
      assert (Hdummy : bc = bc) by reflexivity.
      destruct Hcase as [[Hbc0 _] | (Hbc1 & _ & Hland & Hnp)].
      -
        assert (Hsz : Zlength ents = 0) by lia.
        xruns HR HK 100%nat STOPSR (SCR [false; false; false] [] []) 50%N; [scR DEF8 Hdummy|].
        postrun.
        lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fxc _ _ _ _) _) _ =>
          eapply (FIN fxc R' _ FZb); [ nt_base_from HR' Bd | let Q := fresh in rreg HR' 23%bv Q; exact Q | let Q := fresh in rreg HR' 25%bv Q; exact Q
                                     | let Q := fresh in rreg HR' 26%bv Q; rewrite Q, Hbc0; reflexivity
                                     | let Q := fresh in rreg HR' 22%bv Q; rewrite Q, Hbc0; reflexivity
                                     | let Q := fresh in rreg HR' 10%bv Q; rewrite Q, Hbc0; reflexivity
                                     | let Q := fresh in rreg HR' 1%bv Q; exact Q | left; reflexivity ] end.
      -
        assert (Hmx : 0 <= Z.max (2 * bc + 1) (Zlength ents + 1) < 2 ^ 26) by lia.
        assert (Hl2 : 0 <= Z.land (Z.max (2 * bc + 1) (Zlength ents + 1)) (Z.max (2 * bc + 1) (Zlength ents + 1) - 1) <= 2 ^ 26).
        { split; [apply Z.land_nonneg; lia|]. etransitivity; [apply land_le_l; lia | lia]. }
        destruct (Z.lt_ge_cases (Zlength ents + 1) (2 * bc + 1)) as [Hlt | Hge].
        + rewrite Z.max_l in Hland, Hnp, Hmx, Hl2 by lia.
          xruns HR HK 100%nat STOPSR (SCR [true; true; false] [] []) 50%N; [scR DEF8 Hdummy|].
          postrun.
          lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fxc _ _ _ _) _) _ =>
            eapply (NPK fxc R' Hbc1 FZb); [ nt_base_from HR' Bd | let Q := fresh in rreg HR' 23%bv Q; exact Q | let Q := fresh in rreg HR' 25%bv Q; exact Q
                                          | let Q := fresh in rreg HR' 10%bv Q; rewrite Q, Hnp; reflexivity
                                          | let Q := fresh in rreg HR' 1%bv Q; exact Q ] end.
        + rewrite Z.max_r in Hland, Hnp, Hmx, Hl2 by lia.
          xruns HR HK 100%nat STOPSR (SCR [false; true; false] [] []) 50%N; [scR DEF8 Hdummy|].
          postrun.
          lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fxc _ _ _ _) _) _ =>
            eapply (NPK fxc R' Hbc1 FZb); [ nt_base_from HR' Bd | let Q := fresh in rreg HR' 23%bv Q; exact Q | let Q := fresh in rreg HR' 25%bv Q; exact Q
                                          | let Q := fresh in rreg HR' 10%bv Q; rewrite Q, Hnp; reflexivity
                                          | let Q := fresh in rreg HR' 1%bv Q; exact Q ] end. }

    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (t3c val)]).
    assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (22%bv, EVar 35); (23%bv, EVar 36); (27%bv, EVar 37)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (R1A : forall Rc, base_ok Rc -> getr Rc 22%bv = Z_to_bv 64 bc -> getr Rc 23%bv = Z_to_bv 64 key -> getr Rc 25%bv = Z_to_bv 64 p -> getr Rc 27%bv = Z_to_bv 64 (t3c val) ->
              getr Rc 10%bv = Z_to_bv 64 1 -> getr Rc 11%bv = Z_to_bv 64 (2 * bc) ->
              ((bc = 0 /\ 1 = 1) \/ (bc <> 0 /\ 1 = 1 /\ Z.land (Z.max (2 * bc + 1) (Zlength ents + 1)) (Z.max (2 * bc + 1) (Zlength ents + 1) - 1) <> 0
                                      /\ np_arg bc = Z.max (2 * bc + 1) (Zlength ents + 1))) ->
              srealizes SEGS (cfg fx1 Rc NT_FDIV M model) K).
    { intros Rc Bc Qc22 Qc23 Qc25 Qc27 Qc10 Qc11 Hcase.
      fp_fari MS F_68004 D_68004 FZ Hf14 Hf15 (fun md => div_one_val md (Zlength ents + 1)) 0x68048.
      lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fxc _ _ _ _) _) _ =>
        assert (Hg15 : fholds fxc 15%bv (ieee (Zlength ents + 1))) by (apply fholds_set_same; lia);
        exact (R1BC fxc Rc 1 FZ Hg15 Bc Qc22 Qc23 Qc25 Qc27 Qc10 Qc11 Hcase) end. }
    destruct (Z.eq_dec bc 0) as [Hbc0 | Hbc1]; [| destruct (bseq_pow2 bc HbB Hbc1) as [[Hbc2 Hland] | [Hbc3 Hland]]].
    -
      xruns HR HK 100%nat STOPSR (SCR [true] [] []) 50%N; [split_scs; try sc_auto1|].
      apply R1A; [ nt_base_from HR' B | let Q := fresh in rreg HR' 22%bv Q; exact Q | let Q := fresh in rreg HR' 23%bv Q; exact Q
                 | let Q := fresh in rreg HR' 25%bv Q; exact Q | let Q := fresh in rreg HR' 27%bv Q; exact Q
                 | let Q := fresh in rreg HR' 10%bv Q; exact Q
                 | let Q := fresh in rreg HR' 11%bv Q; rewrite Q; rewrite ?w_mul by lia; f_equal; lia
                 | left; split; [exact Hbc0 | reflexivity] ].
    -
      xruns HR HK 100%nat STOPSR (SCR [true] [] []) 50%N; [split_scs; try sc_auto1|].
      apply R1A; [ nt_base_from HR' B | let Q := fresh in rreg HR' 22%bv Q; exact Q | let Q := fresh in rreg HR' 23%bv Q; exact Q
                 | let Q := fresh in rreg HR' 25%bv Q; exact Q | let Q := fresh in rreg HR' 27%bv Q; exact Q
                 | let Q := fresh in rreg HR' 10%bv Q; exact Q
                 | let Q := fresh in rreg HR' 11%bv Q; rewrite Q; rewrite ?w_mul by lia; f_equal; lia
                 | right; rewrite Hbc2; split; [lia | split; [reflexivity | split; [rewrite Z.max_l by lia; vm_compute; discriminate | rewrite Z.max_l by lia; reflexivity]]] ].
    -
      assert (Hsz : Zlength ents = bc) by lia.
      assert (Hlandr : 0 <= Z.land bc (bc - 1) <= 2 * bc).
      { pose proof (Z.add_lor_land bc (bc - 1)). pose proof (Z.land_nonneg bc (bc - 1)). pose proof (Z.lor_nonneg bc (bc - 1)). lia. }
      assert (Hsl : (0 <? Z.land bc (bc - 1)) = true) by (apply Z.ltb_lt; lia).
      xruns HR HK 100%nat STOPSR (SCR [false] [] []) 50%N; [split_scs; try sc_auto1|].
      apply R1A; [ nt_base_from HR' B | let Q := fresh in rreg HR' 22%bv Q; exact Q | let Q := fresh in rreg HR' 23%bv Q; exact Q
                 | let Q := fresh in rreg HR' 25%bv Q; exact Q | let Q := fresh in rreg HR' 27%bv Q; exact Q
                 | let Q := fresh in rreg HR' 10%bv Q; rewrite Q; nadd; repeat match goal with |- context [?x + -1] => change (x + -1) with (x - 1) end;
                   rewrite ?w_and by lia; rewrite ?w_sltu by lia; rewrite Hsl; reflexivity
                 | let Q := fresh in rreg HR' 11%bv Q; rewrite Q; rewrite ?w_mul by lia; f_equal; lia
                 | right; split; [exact Hbc1 | split; [reflexivity | rewrite Z.max_l by lia; split; [exact (nparg_not_pow2 bc HbB Hbc1) | reflexivity]]] ].
  Qed.

End NtR.

Arguments phaseR1 {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C fx1 p A M model R.
End HNtR.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtD.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibBudget FPSteps SumMemsetLib SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HRepFacts HStmts HConstsS1 HCommon HFpu HFind HBlk HNtCtx. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtA.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtA.HNtS. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HNtA.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNt.HNtF. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNt.HNtR. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HNtD S1_code_67e94_68324.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition STOPSG : list Z := [NT_INS].

#[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

Section Nt.
Context {AC : AllocCeiling}.

  Variables (L : Layout) (MI : MallocIface SEGS L) (ST : StaticsIface SEGS L) (NEW_STACK DEL_STACK : Z).
  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp parser key bl bc : Z) (val : Z * Z * Z) (v2 : Z) (ents : list (Z * (Z * (Z * Z * Z)))) (K : TSet).
  Variable C : @ntctx AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K.
  #[local] Abbreviation NTS := (NT_STACK NEW_STACK DEL_STACK).
  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI (c_HLimg_lo C) (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST (c_HLimg_lo C) (c_HLrw_img C) (c_HLrelro_img C) (c_HLrw_relro C) (c_HLerr_rw C)).
  #[local] Abbreviation ro_clear_via_eff' := (ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation agree_block_via_eff' := (agree_block_via_eff L MI (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation own_sx_via_eff' := (own_sx_via_eff L MI ST (c_HLrw_img C)).
  #[local] Abbreviation hi_unowned' := (hi_unowned L MI (c_HLimg_lo C) (c_HLrw_img C)).
  #[local] Abbreviation obj := (parser + 136).
  #[local] Abbreviation sent := (parser + 152).
  #[local] Abbreviation W := (Wnt NEW_STACK DEL_STACK sp).
  #[local] Abbreviation base_ok := (nt_base_ok L R0 sp parser val v2).
  #[local] Abbreviation pframe := (nt_pframe sp parser key).
  #[local] Abbreviation SPF := (sp_facts C).
  #[local] Abbreviation BCF := (bc_facts C).
  #[local] Ltac ctx := ntctx_pose C.

  #[local] Abbreviation core := (@HNtA.core AC L MI ST NEW_STACK DEL_STACK A0 s R0 model0 sp parser key val v2).
  #[local] Abbreviation nst := (@HNtA.nst AC L MI ST NEW_STACK DEL_STACK A0 s R0 M0 model0 sp parser key bl bc val v2 ents).
  #[local] Abbreviation rcall := (@HNtR.rcall AC L MI ST NEW_STACK DEL_STACK A0 s R0 M0 model0 sp parser key bl bc val v2 ents).
  #[local] Abbreviation dbase := (@HNtD.dbase L R0 sp parser key val v2).

  Ltac scE Hland Hj DEFp HDEF DEFbl :=
    split_scs;
    lazymatch goal with
    | |- sc_denot _ _ _ (SCStoreOk _ _) =>
        eapply sc_storeok; [evs; nrw Hj; reflexivity | lia | cbn [a_off]; lia | cbn [a_off]; lia
                          | cbn [a_off]; rewrite ?Z.add_0_r;
                            first [ lazymatch goal with |- defined _ ?a _ => match goal with D : defined _ a _ |- _ => eapply (defined_sub _ _ _ _ _ D); lia end end
                                  | eapply (defined_sub _ _ _ _ _ HDEF); lia | eapply (defined_sub _ _ _ _ _ DEFp); lia | eapply (defined_sub _ _ _ _ _ DEFbl); lia] ]
    | |- sc_denot _ _ _ (SCFlat _ _) => eapply sc_flat; [evs; nrw Hj; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]
    | |- sc_denot _ _ _ (SCBr _ _ _ _) => cbn [sc_denot]; evs; nrw Hj; rewrite ?Hland; rewrite ?br_ne, ?br_eq, ?br_ltu, ?br_geu, ?br_eq_sxw, ?br_ne_sxw by lia; bool_lia
    | |- sc_denot _ _ _ (SCReadBase _ _ _ _) =>
        first [ match goal with H : cellw _ _ _ _ _ |- _ =>
                  eapply (sc_read_cellw _ _ _ _ _ _ _ _ H); [first [apply N.le_refl | cbn; lia] | evs; nrw Hj; first [reflexivity | f_equal; lia] | evs; reflexivity] end
              | sc_auto1 ]
    | |- _ => sc_auto1
    end.

  Lemma phaseR2 : forall (fx2 : FPState) p A M model R,
    frm_zero (@fp_csr fx2) -> rcall p A M model R -> srealizes SEGS (cfg fx2 R NT_NEWE M model) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros fx2 p A M model R FZ RCL.
    destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
    destruct BCF as (HbB & Hbcr & Hload & Hsz0). pose proof (proj1 (nf_key _ _ _ _ _ _ _ _ _ NF)) as Hkr. cbn in Hkr.
    destruct (bseq_next_facts bc HbB Hlast) as (HnB & Hbcn & Hn28 & Hncase).
    set (n := bseq_next bc) in *.
    destruct RCL as [AI MS Hfs Hfds SX B Q23 Q25 Q26 Q22 Q10 Q1 FR DEF8 DEFW SPILL Hp0 Hpc Hpal Hpl Hpnew Cnh Cnk DEFp EFF LADD U Hgrow RC].
    pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
    assert (FOFF : forall a, (p <= a < p + 32 \/ sp + 8 <= a < sp + 16) -> ~ in_ranges (ly_img L) a).
    { intros a [Ha | Ha] Hi; [exact (live_offimg' A M model p 32 a AI Hpl Ha Hi) | pose proof (HLimg_lo _ Hi); lia]. }
    pose proof (own_sx_via_eff' A0 A M0 M W _ EFF Hown_sx FOFF) as OSX.
    destruct FR as (F1 & F2 & F3 & F4 & F5 & F6).
    eapply (rehash_inl C fx2 A M model R p AI MS Hfs Hfds SX RC OSX (conj B (conj Q23 Q25)) Q26 Q22 Q10 Q1 U DEFW F2).
    - pose proof (ROOM2 Hgrow) as RM. unfold roomL in RM |- *. rewrite (proj1 LADD). cbn [count_class_f big_bytes_f] in RM |- *.
      rewrite (ef_caps _ _ _ _ _ _ _ _ _ EFF), (ef_bigcap _ _ _ _ _ _ _ _ _ EFF). exact RM.
    -
      intros A' R' M' model' bl' ents' AI' MS' Hfs' Hfds' DB' U' PERM' LAP' EFF' DEFW'.
      destruct DB' as (BR & Q23' & Q25'). pose proof BR as BR'. destruct BR' as (C2 & C3 & C4 & C8 & C24 & C21 & C18 & Cs).
      assert (Hlen : Zlength ents' = Zlength ents) by (unfold Zlength; rewrite (Permutation_length PERM'); reflexivity).
      pose proof (u_bseq U') as HnB'. pose proof (u_bl_lo U' ltac:(lia)) as Hbl'0. pose proof (u_bl_hi U') as Hbl'1.

      destruct LAP' as (lv1 & LADD' & LAP2).
      assert (Hpbl' : p <> bl') by (intros ->; apply (proj2 LADD'); apply (in_map fst _ (bl', 32)); exact Hpl).
      assert (Hpl' : In (p, 32) (live MI A')).
      { assert (H1 : In (p, 32) lv1) by (rewrite (proj1 LADD'); right; exact Hpl).
        destruct (Z.eqb_spec bc 0) as [Hb0|Hb1]; cbn [lapply] in LAP2.
        - rewrite LAP2. exact H1.
        - destruct LAP2 as (lv2 & DELb & ->). apply (proj2 (DELb p 32)). split; [exact H1|].
          intros ->. apply Hpnew. destruct (u_blive U0) as [[? ?]|[_ Hin]]; [lia|]. apply (in_map fst _ (bl, 8 * bc)). exact Hin. }
      assert (Hpa' : forall q m, In (q, m) (umap_blocks 32 bl' n ents') -> apart p 32 q m).
      { intros q m Hq. unfold umap_blocks in Hq. apply in_app_iff in Hq. destruct Hq as [Hq | Hq].
        - destruct (Z.eqb_spec n 0); [destruct Hq|]. destruct Hq as [Hq|[]]. injection Hq as <- <-.
          destruct (u_blive U') as [[? ?]|[_ Hin]]; [lia|].
          exact (ai_live_disjoint MI A' M' model' p 32 bl' (8 * n) AI' Hpl' Hin Hpbl').
        - apply in_map_iff in Hq. destruct Hq as ([q' [k v]] & Hq' & Hin). cbn in Hq'. injection Hq' as <- <-.
          assert (Hin0 : In (q', (k, v)) ents) by (eapply Permutation_in; [exact PERM' | exact Hin]).
          apply (ai_live_disjoint MI A' M' model' p 32 q' 32 AI' Hpl' (proj1 (u_node U' q' k v Hin))).
          intros <-. apply Hpnew. apply (in_map fst _ (p, 32)). exact (proj1 (u_node U0 p k v Hin0)). }
      assert (HFp : forall a, umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl' n ents' a -> ~ (p <= a < p + 32)).
      { intros a [Ha | Ha]; [exact (foot_apart_new C A M model p 32 a AI LADD Ha)|].
        intros Hpa. destruct (umap_foot_hb 32 obj bl' n ents' a Ha) as [Hh | ([q m] & Hq & Hqa)]; [lia|]. cbn in Hqa.
        pose proof (Hpa' q m Hq) as Hap. unfold apart in Hap.
        assert (Hm : 0 < m).
        { unfold umap_blocks in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
          - destruct (Z.eqb_spec n 0); [destruct Hq|]. destruct Hq as [Hq|[]]. injection Hq as <- <-. lia.
          - apply in_map_iff in Hq. destruct Hq as (e & He & _). injection He as _ <-. lia. }
        lia. }
      assert (Hflh : forall a, umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl' n ents' a -> a + 1 <= alloc_ceiling \/ obj <= a < obj + 40).
      { assert (FLH : forall Ax Mx modelx blx bcx entsx a, ainv MI Ax Mx modelx -> umapx MI 32 (nval32 SEGS) Ax Mx obj blx bcx entsx ->
                      umap_foot 32 obj blx bcx entsx a -> a + 1 <= alloc_ceiling \/ obj <= a < obj + 40).
        { intros Ax Mx modelx blx bcx entsx a AIx Ux [Hh | [[Hbc Hb] | (q & Hq & Hqa)]]; [right; exact Hh | left | left].
          - destruct (u_blive Ux) as [[? ?]|[_ Hin]]; [lia|]. destruct (live_facts' Ax Mx modelx blx (8 * bcx) AIx Hin) as (_ & _ & Hc & _). lia.
          - apply in_map_iff in Hq. destruct Hq as ([q' [k v]] & Hq' & Hin). cbn in Hq'. subst q'.
            destruct (live_facts' Ax Mx modelx q 32 AIx (proj1 (u_node Ux q k v Hin))) as (_ & _ & Hc & _). lia. }
        intros a [Hf | Hf]; [exact (FLH A M model bl bc ents a AI U Hf) | exact (FLH A' M' model' bl' n ents' a AI' U' Hf)]. }
      assert (AGp : agree_on M M' p 32).
      { eapply (agree_block_via_eff' A A' M M' model model'); [exact EFF' | exact AI | exact AI' | exact Hpl | exact Hpl' | | cbn; lia].
        intros a Ha Hf. exact (HFp a Hf Ha). }
      assert (AGa : forall a k, sp <= a -> a + k <= sp + 248 -> 0 <= k -> (forall i, 0 <= i < k -> ~ owned MI A (a + i)) -> defined M a k -> agree_on M M' a k).
      { intros a k Ha Hak Hk Hown Hdef. eapply (agree_above_via_eff' A A' M M' _ _ a k sp EFF'); [lia | cbn; lia | lia | lia | lia | exact Hown | exact Hdef |].
        intros i Hi Hf. destruct (Hflh _ Hf); lia. }
      assert (Hhiown : forall a k i, alloc_ceiling <= a -> 0 <= i < k -> ~ owned MI A (a + i)) by (intros a k i Ha Hi; eapply hi_unowned'; [exact AI | lia]).
      assert (AGc : forall a v, cell8 SEGS M a v -> sp <= a -> a + 8 <= sp + 248 -> cell8 SEGS M' a v).
      { intros a v F Ha1 Ha2. eapply cellw_agree; [exact F | | lia | cbn; lia].
        apply AGa; [lia | lia | lia | intros i Hi; apply (Hhiown a 8 i); lia | exact (cellw_high_defined M a 8 _ F ltac:(lia) ltac:(cbn; lia))]. }
      assert (SPILL' : cell8 SEGS M' (sp + 8) (t3c val)) by (apply AGc; [exact SPILL | lia | lia]).
      assert (FR' : pframe M').
      { split; [| split; [|split; [|split; [|split]]]]; try (apply AGc; [assumption | lia | lia]).
        eapply cellw_agree; [exact F1 | | lia | cbn; lia].
        apply AGa; [lia | lia | lia | intros i Hi; apply (Hhiown (sp + 244) 4 i); lia | exact (cellw_high_defined M (sp + 244) 4 _ F1 ltac:(lia) ltac:(cbn; lia))]. }
      assert (EFF2 : eff MI A0 A' M0 M' W (fun a => (p <= a < p + 32 \/ sp + 8 <= a < sp + 16) \/ (umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl' n ents' a))).
      { eapply eff_trans; [exact EFF | exact EFF' | intros a Ha; eapply hi_unowned'; [exact AI' | unfold W_of, Wnt in Ha; cbn in Ha; lia]]. }
      assert (FOFF2 : forall a, (p <= a < p + 32 \/ sp + 8 <= a < sp + 16) \/ (umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl' n ents' a) -> ~ in_ranges (ly_img L) a).
      { intros a [Ha | [Ha | Ha]]; [exact (FOFF a Ha) | exact (foot_offimg_gen C A M model bl bc ents a AI U Ha) | exact (foot_offimg_gen C A' M' model' bl' n ents' a AI' U' Ha)]. }
      assert (SX' : sx_inv ST s M').
      { eapply (sx_inv_via_eff' s A0 A' M0 M' model0 W _ SX0 AI0 EFF2 Hown_sx Herr_sx FOFF2). unfold Wnt; cbn; lia. }
      assert (Hch : 0 <= hmod key n < n) by (unfold hmod; apply Z.mod_pos_bound; lia).
      pose proof (h_bc (u_hdr U')) as Cbc'. unfold cell8 in Cbc'. pose proof SPILL' as SP8. unfold cell8 in SP8.

      assert (FINR : forall R5,
        base_ok R5 -> getr R5 23%bv = Z_to_bv 64 key -> getr R5 25%bv = Z_to_bv 64 p ->
        getr R5 22%bv = Z_to_bv 64 n -> getr R5 26%bv = Z_to_bv 64 (hmod key n) -> getr R5 27%bv = Z_to_bv 64 (t3c val) ->
        srealizes SEGS (cfg fx2 R5 NT_INS M' model') K).
      { intros R5 B5 Q23'' Q25'' Q22'' Q26'' Q27''.
        assert (CO : core p A' M' model' R5).
        { constructor.
          - exact AI'. - exact MS'. - exact Hfs'. - exact Hfds'. - exact SX'.
          - exact B5. - exact Q23''. - exact Q25''.
          - exact FR'.
          - eapply defined_agree; [exact DEF8 | apply AGa; [lia | lia | lia | intros i Hi; apply (Hhiown (sp + 8) 8 i); lia | exact DEF8]].
          - exact DEFW'.
          - exact Hp0. - exact Hpc. - exact Hpal. - exact Hpl'. - exact Hpnew.
          - eapply cellw_agree; [exact Cnh | eapply agree_on_sub; [exact AGp | lia | cbn; lia] | lia | cbn; lia].
          - eapply cellw_agree; [exact Cnk | eapply agree_on_sub; [exact AGp | lia | cbn; lia] | lia | cbn; lia].
          - eapply defined_agree; [exact DEFp | exact AGp]. }
        eapply (phaseF C fx2 p A' M' model' R5 bl' n ents' true _ CO FZ ltac:(lia) ltac:(lia) Q22'' Q26'' Q27'' U' PERM' Hpa').
        + intros HT. discriminate HT.
        + intros _. split; [exact Hgrow | reflexivity].
        + cbn [app]. exists (live MI A). split; [exact LADD|]. exists lv1. split; [exact LADD' | exact LAP2].
        + exact EFF2.
        + intros a [[Ha | Ha] | [Ha | Ha]]; [left; exact Ha | right; right; right; exact Ha | right; left; exact Ha | right; right; left; exact Ha].
        + exact FOFF2. }

      pose (E := Eseed R' [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 key; Z_to_bv 64 n; Z_to_bv 64 (t3c val)]).
      assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (23%bv, EVar 35)]) R').
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M' []) by constructor.
      assert (Hlandr : 0 <= Z.land n (n - 1) <= 2 * n).
      { pose proof (Z.add_lor_land n (n - 1)). pose proof (Z.land_nonneg n (n - 1)). pose proof (Z.lor_nonneg n (n - 1)). lia. }
      assert (Hdummy : bl' = bl') by reflexivity.
      Ltac finR FINR HR' BR Hj Hd :=
        eapply FINR;
        [ nt_base_from HR' BR
        | let Q := fresh in rreg HR' 23%bv Q; exact Q
        | let Q := fresh in rreg HR' 25%bv Q; exact Q
        | let Q := fresh in rreg HR' 22%bv Q; exact Q
        | let Q := fresh in rreg HR' 26%bv Q; rewrite Q; nrw Hd; first [reflexivity | f_equal; first [exact Hj | lia]]
        | let Q := fresh in rreg HR' 27%bv Q; exact Q ].
      clear - HR HK FINR MS' BR Cbc' SP8 Hkr Hbl'0 Hbl'1 Hch Hobjlo Hobjhi Hsphi Hsplo Hn16 HnN HnD Hs1 Hpar Hp0 Hpc Hcl Hcv HnB Hbcn Hn28 Hlandr Hncase Hdummy Hv3.
      destruct Hncase as [[Hbc0 Hn2] | [Hn3 Hland]].
      +
        assert (Hland : Z.land n (n - 1) = 0) by (rewrite Hn2; reflexivity).
        assert (Hj : Z.land (n - 1) key = hmod key n) by (rewrite Hn2; change (2 - 1) with 1; rewrite Z.land_comm, land_1; reflexivity).
        xruns HR HK 100%nat STOPSG (SCR [false] [EVar 36; EVar 37] []) 50%N; [scE Hland Hdummy Hdummy Hdummy Hdummy|].
        finR FINR HR' BR Hj Hdummy.
      + destruct (Z.lt_ge_cases key n) as [Hlt | Hge].
        * assert (Hj : key = hmod key n) by (unfold hmod; rewrite Z.mod_small by lia; reflexivity).
          xruns HR HK 100%nat STOPSG (SCR [true; false] [EVar 36; EVar 37] []) 50%N; [scE Hland Hdummy Hdummy Hdummy Hdummy|].
          finR FINR HR' BR Hj Hdummy.
        * pose proof Hch as Hch'. unfold hmod in Hch'.
          assert (Hj : key mod n = hmod key n) by reflexivity.
          xruns HR HK 100%nat STOPSG (SCR [true; true] [EVar 36; EVar 37] []) 50%N; [scE Hland Hdummy Hdummy Hdummy Hdummy|].
          finR FINR HR' BR Hj Hdummy.
  Qed.

  Theorem nt_correct : srealizes SEGS (cfg fx R0 NT_ENTRY M0 model0) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ac_bounds_lit as Hcv.
    destruct (pframe0 C) as (F1 & F2 & F3 & F4 & F5 & F6). destruct (base0 C) as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
    destruct (nsearch_correct L MI (seg_rom SEGS) A0 M0 parser sp bl bc key ents U0 F1 F3 F4 F5 F6 ltac:(lia) ltac:(lia) ltac:(lia) R0 B8 B2 B24)
      as (R1 & KEEP & SR & G26 & CASES).
    destruct SR as (T8 & T2 & T24 & T22 & T23).
    assert (B1 : base_ok R1).
    { unfold nt_base_ok. split; [exact T2|]. split; [rewrite (KEEP 3%bv) by (unfold nkeep_regs; inl); exact B3|]. split; [rewrite (KEEP 4%bv) by (unfold nkeep_regs; inl); exact B4|].
      split; [exact T8|]. split; [exact T24|]. split; [rewrite (KEEP 21%bv) by (unfold nkeep_regs; inl); exact B21|]. split; [rewrite (KEEP 18%bv) by (unfold nkeep_regs; inl); exact B18|].
      intros r Hr. rewrite KEEP; [reflexivity|]. clear - Hr. unfold nkeep_regs. cbn in Hr |- *. intuition congruence. }
    assert (Q27 : getr R1 27%bv = Z_to_bv 64 (t3c val)) by (rewrite (KEEP 27%bv) by (unfold nkeep_regs; inl); exact (nf_s11 _ _ _ _ _ _ _ _ _ NF)).
    destruct CASES as [(p & v0 & Hin & Hms & G25) | Hms].
    -
      eapply srz_msteps; [eapply ms_halt; exact MS0 | eapply ms_lazy; exact MS0 | exact Hms |].
      destruct (in_split _ _ Hin) as (l1 & l2 & HE).
      exact (phaseV C R1 p v0 l1 l2 B1 Q27 G25 HE).
    -
      eapply srz_msteps; [eapply ms_halt; exact MS0 | eapply ms_lazy; exact MS0 | exact Hms |].
      apply (phaseN C R1 B1 T22 T23 G26 Q27). intros p A2 M2 model2 R2 NS.
      apply (phaseI C p A2 M2 model2 R2 NS).
      +
        intros fx1 M' R' CO Q22 Q26 Q27' FZ Hf14 Hf15 Hgrow EFF LADD U RC.
        apply (phaseR1 C fx1 p A2 M' model2 R' CO Q22 Q27' FZ Hf14 Hf15 Hgrow EFF LADD U RC).
        intros fx2 M'' R'' FZ2 RCL. exact (phaseR2 fx2 p A2 M'' model2 R'' FZ2 RCL).
      +
        intros fx1 M' R' CO FZ Hbc1 Hload Q22 Q26 Q27' EFF LADD U RC.
        destruct CO as [AI MS Hfs Hfds SX B Q23 Q25 FR DEF8 DEFW Hp0 Hpc Hpal Hpl Hpnew Cnh Cnk DEFp] eqn:HCO. clear HCO.
        eapply (phaseF C fx1 p A2 M' model2 R' bl bc ents false _ CO FZ Hbc1 Hload Q22 Q26 Q27' U (Permutation_refl _)
                  (blocks_apart_p C p A2 M' model2 AI LADD)).
        * intros _. split; reflexivity.
        * intros HT. discriminate HT.
        * cbn [app]. exists (live MI A2). split; [exact LADD | reflexivity].
        * exact EFF.
        * intros a Ha. left. exact Ha.
        * intros a Ha. exact (live_offimg' A2 M' model2 p 32 a AI Hpl Ha).
  Qed.

End Nt.

Arguments nt_correct {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C.

Theorem emplace_nt_block_spec {AC : AllocCeiling} :
  forall (L : Layout) (MI : MallocIface SEGS L) (ST : StaticsIface SEGS L) (NEW_STACK DEL_STACK : Z),
    0 <= NEW_STACK -> 0 <= DEL_STACK ->
    new_rule_stmt SEGS L MI ST NEW_STACK -> delete_rule_stmt SEGS L MI DEL_STACK ->
    next_prime_stmt SEGS L hc -> memset_stmt SEGS hc ->
    ly_new L = NT_NEWE -> ly_delete L = NT_DELETE ->
    (forall a, in_ranges (ly_img L) a -> a < alloc_ceiling) ->
    (forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a) ->
    (forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a) ->
    (forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a) ->
    (forall a, errno_win L a -> in_ranges (ly_rw L) a) ->
    emplace_nt_block_stmt SEGS L MI ST hc NEW_STACK DEL_STACK.
Proof.
  intros L MI ST NEW_STACK DEL_STACK NSnn DSnn NEW DEL NP MEMSETH HLnew HLdel HL1 HL2 HL3 HL4 HL5.
  unfold emplace_nt_block_stmt.
  intros fx A s R M model sp parser key bl bc val v2 ents K AI MS SX SXH Hsp16 Hceil Hroom Hwin Hosx Hesx FRM NF ASP8 ASP24 ASP244 SO8 U ASPT HPAR Hv1 Hv2 Hv3 Hv2r Hv2m ROC HSZ HNMAX Hlast ROOM1 ROOM2 CONT.
  change (hc_nt_entry hc) with NT_ENTRY.
  apply (@nt_correct AC L MI ST NEW_STACK DEL_STACK fx A s R M model sp parser key bl bc val v2 ents K).
  constructor; try assumption.
Qed.
