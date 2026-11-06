(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ldh OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8Lf.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Le.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys7c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ldh.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).





Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  Hypothesis N3F : N3F_stmt bt.
  Hypothesis N3U : N3U_stmt bt.
  (* [comment removed for export] *)
  Hypothesis N3FH : AsKSys10.AsKSys7c.N3FH_stmt bt.
  Hypothesis N3UH : AsKSys10.AsKSys7c.N3UH_stmt bt.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).
  #[local] Abbreviation IA := (bt_ia bt).

  (* [comment removed for export] *)
  Definition um_st (st : ast) (c : Z) : ast :=
    add_meter (op_usermap st c) 0 [(sh_lo (region_beg SBEG c + r_mapped_user (a_reg st c)), sh_lo (region_beg SBEG c + r_mapped_user (a_reg st c)) + KUSERMAP / 8)] 0.
  Definition pop_st (st : ast) (c : Z) (um fm : bool) : ast := bc_st bt (if um then um_st st c else st) c fm.

  (* [comment removed for export] *)
  Definition pop_zone (st : ast) (c : Z) (z : Z) : Prop :=
    let ulo := region_beg SBEG c + r_mapped_user (a_reg st c) in let flo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    (ulo <= z < ulo + KUSERMAP) \/ (sh_lo ulo <= z < sh_lo ulo + KUSERMAP / 8)
    \/ (fa_beg SBEG c <= z < flo + KFAMAP) \/ (sh_lo flo <= z < sh_lo flo + KFAMAP / 8).
  (* [comment removed for export] *)
  Definition pop_zone_t (st : ast) (c : Z) (z : Z) : Prop :=
    let ulo := region_beg SBEG c + r_mapped_user (a_reg st c) in let flo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    (ulo <= z < ulo + KUSERMAP) \/ (sh_lo ulo <= z < sh_lo ulo + KUSERMAP / 8)
    \/ (fa_beg SBEG c <= z < flo)
    \/ (r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 /\ ((flo <= z < flo + KFAMAP) \/ (sh_lo flo <= z < sh_lo flo + KFAMAP / 8))).
  Lemma pop_zone_t_sub : forall st c z, 0 <= r_mapped_fa (a_reg st c) -> pop_zone_t st c z -> pop_zone st c z.
  Proof using.
    intros st c z MF0 PZ. unfold pop_zone_t in PZ. (lazymatch goal with |- ?G => let G' := eval unfold pop_zone in G in change_no_check G' end). cbv zeta in *.
    destruct PZ as [P | [P | [P | [_ [P | P]]]]]; [left; exact P | right; left; exact P | right; right; left | right; right; left | right; right; right; exact P].
    - destruct P as [P1 P2]. split; [exact P1 | (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); lia].
    - destruct P as [P1 P2]. split; [lia | exact P2].
  Qed.
  (* [comment removed for export] *)
  Definition pop_foot (st : ast) (c : Z) (sp : Z) (z : Z) : Prop :=
    (sp - 512 <= z < sp) \/ pop_zone_t st c z \/ (T + 2792 <= z < T + 2888) \/ (reginfo bt c + 16 <= z < reginfo bt c + 128).

  Lemma um_st_reg : forall st c, a_reg (um_st st c) c
      = REG (r_mapped_user (a_reg st c) + KUSERMAP) (r_alloc_user (a_reg st c)) (r_mapped_fa (a_reg st c)) (r_free (a_reg st c)) false (r_fhole (a_reg st c))
    /\ a_cinit (um_st st c) = a_cinit st.
  Proof using. intros st c. (lazymatch goal with |- ?G => let G' := eval unfold um_st, op_usermap, set_reg, add_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). rewrite Z.eqb_refl. split; reflexivity. Qed.

  Theorem populateM_katsD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v s6v tp gp : word) (req : Z) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cinit st = true -> a_kact st <= KCAP -> mu_room st ->
    let r := a_reg st c in let au := r_alloc_user r in let mu := r_mapped_user r in let nf := Z.of_nat (length (r_free r)) in let mfa := r_mapped_fa r in
    (* [comment removed for export] *)
    a_cache st c = [] -> nf < cache_hint c ->
    (forall z, X z -> ~ pop_zone_t st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160) /\ ~ (reginfo bt c <= z < reginfo bt c + 128)) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 0x103f18 ->
    getr regs 11 = at_ (Z_to_bv 64 T) 2768 -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 (reginfo bt c) -> getr regs 14 = Z_to_bv 64 req ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    (CEIL + 512 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> (1 <= req /\ csize c * req <= 2 ^ 18) -> mu < au + csize c * req ->
    writableZ ASEGS M (U sp - 512) (U sp) ->
    (forall (fm : bool) (r' : bvmap 5 word) (M' : mem) mdl',
        (fm = false -> ~ ftest (um_st st c) c) ->
        WF bt (pop_st st c true fm) Lc FF -> RepX bt (XL c) (pop_st st c true fm) Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> pop_foot st c (U sp) (U a) /\ M' a <> None) ->
        pf_ret sp ra s0v s1v s2v s3v s4v s5v s6v tp gp 1 r' ->
        katwD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ st' = op_uhole st c \/ st' = um_st st c \/ (st' = op_fhole (um_st st c) c /\ ftest (um_st st c) c)) ->
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> pop_foot st c (U sp) (U a) /\ (M' a <> None \/ pop_zone_t st c (U a))) ->
        pf_ret sp ra s0v s1v s2v s3v s4v s5v s6v tp gp 0 r' ->
        katD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qf) ->
    katsD ASEGS (mkCfg (mkst regs (0x50dd4%bv : word) M rom) mdl) Qok Qf.
  Proof using N3UH N3FH N3U N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v s6v tp gp req Qok Qf Hc W RX HALT MW CINIT KC MUR r au mu nf mfa HC0 NFH XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 Hsp Hret Hreq Hmap WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    pose proof (csize_pos c Hc) as [CS1 CS2].
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((Y1a & Y1b) & _). fold r mu au in Y1a, Y1b.
    set (ulo := region_beg SBEG c + mu). set (flo := fa_beg SBEG c + mfa).
    assert (MFA0 : 0 <= mfa) by (pose proof (region_facts bt st Lc FF W c Hc) as RF; cbn zeta in RF; fold r mfa in RF; destruct RF as (_ & _ & _ & _ & _ & E6 & _); lia).
    destruct (r_uhole (a_reg st c)) eqn:UH.
    {     apply (popAm_katsD_h bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3UH c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v s6v tp gp req Qok Qf
             Hc W RX HALT MW UH KC MUR).
    - intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & X3 & X4). fold r mu ulo.
      split; [exact X4|]. split; [exact X2|]. split; [exact X3|]. unfold pop_zone_t in X1. fold r mu mfa ulo flo in X1.
      split; intros Hin; apply X1; [left; exact Hin | right; left; exact Hin].
    - exact H1. - exact H2. - exact H4. - exact H3. - exact Etp. - exact H10. - exact H11. - exact H12. - exact H13. - exact H14.
    - exact H8. - exact H9. - exact H18. - exact H19. - exact H20. - exact H21. - exact H22.
    - split; lia.
    - exact Hret.
    - exact Hreq.
    - exact Hmap.
    - intros i Hi. apply WSTK. lia.
    - (* [comment removed for export] *)
      intros r1 M1 mdl1. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold r mu au nf ulo. intros W1 RX1 SEV1 LK1 MW1 HL1 FOOT1 SL1 PR1 A1 A10 A11 A12 A13 A9 A19 A20 A4 A3.
      change (add_meter (op_usermap st c) 0 [(sh_lo ulo, sh_lo ulo + KUSERMAP / 8)] 0) with (um_st st c) in W1, RX1.
      destruct (um_st_reg st c) as [EREG ECI]. fold r mu au mfa in EREG.
      assert (WST1 : writableZ ASEGS M1 (U sp - 512) (U sp - 64)).
      { intros i Hi. apply (repx_wr (fun _ => True) M1 M (fun a Ha => conj I (proj2 (FOOT1 a Ha))) (U sp - 512) (U sp) ltac:(lia) ltac:(lia) WSTK). lia. }
      apply (popBC_katwD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3FH c (um_st st c) Lc FF M1 rom mdl1 r1 sp ra s0v s1v s2v s3v s4v s5v s6v tp gp Qok Qf
               Hc W1 RX1 HL1 MW1 ltac:(rewrite ECI; exact CINIT) ltac:((lazymatch goal with |- ?G => let G' := eval unfold um_st in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); rewrite Z.add_0_r; exact KC)).
      + exact HC0.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_free] in G in change_no_check G' end). exact NFH.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). lia.
      + intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & X3 & X4). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_fa] in G in change_no_check G' end). fold flo.
        split; [exact X4|]. split; [exact X2|]. split; [exact X3|]. unfold pop_zone_t in X1. fold r mu mfa ulo flo in X1.
        split; [intros Hin; apply X1; right; right; left; exact Hin|].
        intros RM. split; intros Hin; apply X1; do 3 right; (split; [exact RM|]); [left; exact Hin | right; exact Hin].
      + exact PR1. + exact A1. + exact A10. + exact A11. + exact A12.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_free] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end). fold nf. (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). exact A13.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_free] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end). fold nf. (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). exact A9.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). exact A19.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). exact A20.
      + exact A4. + exact A3. + exact Etp.
      + split; lia.
      + exact Hret.
      + exact SL1.
      + exact WST1.
      + intros fm r' M' mdl' NFT. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_fa] in G in change_no_check G' end). fold flo. intros W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 PRET.
        apply (CONT1 fm r' M' mdl' NFT W2 RX2 (same_except_vm_trans _ _ _ SEV1 SEV2)); [ | exact MW2 | exact HL2 | | exact PRET].
        * intros a Ha. rewrite (LK2 a Ha). exact (LK1 a Ha).
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold pop_foot, pop_zone_t in G in change_no_check G' end). fold r mu mfa ulo flo.
          destruct (decide (M' a = M1 a)) as [E | NE].
          -- rewrite E in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. split; [| exact Dd]. clear - F. lia.
          -- destruct (FOOT2 a NE) as [F Dd]. split; [| exact Dd]. clear - F. lia.
      + intros r' M' mdl' st'. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_fa] in G in change_no_check G' end). fold flo. intros EST W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 PRET0.
        apply (CONT0 r' M' mdl' st' ltac:(destruct EST as [-> | [-> FT]]; [right; right; left; reflexivity | right; right; right; split; [reflexivity | exact FT]]) W2 RX2 (same_except_vm_trans _ _ _ SEV1 SEV2));
          [ | exact MW2 | exact HL2 | | exact PRET0].
        * intros a Ha. rewrite (LK2 a Ha). exact (LK1 a Ha).
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold pop_foot, pop_zone_t in G in change_no_check G' end). fold r mu mfa ulo flo.
          destruct (decide (M' a = M1 a)) as [E | NE].
          -- rewrite E in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. split; [clear - F; lia | left; exact Dd].
          -- destruct (FOOT2 a NE) as [[F Dd] | F]; [split; [clear - F; lia | left; exact Dd] | split; [unfold flo in *; clear - F MFA0; lia | right; unfold flo in *; clear - F MFA0; lia]].
    - (* [comment removed for export] *)
      intros r0 r' M' mdl' st'. fold r mu ulo. intros EST W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 AG (P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & PAG).
      apply (CONT0 r' M' mdl' st' ltac:(destruct EST as [-> | ->]; [left; reflexivity | right; left; reflexivity]) W2 RX2 SEV2 LK2 MW2 HL2);
        [ | (lazymatch goal with |- ?G => let G' := eval unfold pf_ret in G in change_no_check G' end); repeat (split; [assumption|]);
            split; [rewrite (PAG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi);
                    rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); exact H4
                   | rewrite (PAG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi);
                     rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); exact H3]].
      intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold pop_foot, pop_zone_t in G in change_no_check G' end). fold r mu mfa ulo flo. destruct (FOOT2 a Ha) as [[F Dd] | F]; [split; [clear - F; lia | left; exact Dd] | split; [clear - F; lia | right; clear - F; lia]]. }
    {     apply (popAm_katsD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3U c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v s6v tp gp req Qok Qf
             Hc W RX HALT MW UH KC MUR).
    - intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & X3 & X4). fold r mu ulo.
      split; [exact X4|]. split; [exact X2|]. split; [exact X3|]. unfold pop_zone_t in X1. fold r mu mfa ulo flo in X1.
      split; intros Hin; apply X1; [left; exact Hin | right; left; exact Hin].
    - exact H1. - exact H2. - exact H4. - exact H3. - exact Etp. - exact H10. - exact H11. - exact H12. - exact H13. - exact H14.
    - exact H8. - exact H9. - exact H18. - exact H19. - exact H20. - exact H21. - exact H22.
    - split; lia.
    - exact Hret.
    - exact Hreq.
    - exact Hmap.
    - intros i Hi. apply WSTK. lia.
    - (* [comment removed for export] *)
      intros r1 M1 mdl1. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold r mu au nf ulo. intros W1 RX1 SEV1 LK1 MW1 HL1 FOOT1 SL1 PR1 A1 A10 A11 A12 A13 A9 A19 A20 A4 A3.
      change (add_meter (op_usermap st c) 0 [(sh_lo ulo, sh_lo ulo + KUSERMAP / 8)] 0) with (um_st st c) in W1, RX1.
      destruct (um_st_reg st c) as [EREG ECI]. fold r mu au mfa in EREG.
      assert (WST1 : writableZ ASEGS M1 (U sp - 512) (U sp - 64)).
      { intros i Hi. apply (repx_wr (fun _ => True) M1 M (fun a Ha => conj I (proj2 (FOOT1 a Ha))) (U sp - 512) (U sp) ltac:(lia) ltac:(lia) WSTK). lia. }
      apply (popBC_katwD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3FH c (um_st st c) Lc FF M1 rom mdl1 r1 sp ra s0v s1v s2v s3v s4v s5v s6v tp gp Qok Qf
               Hc W1 RX1 HL1 MW1 ltac:(rewrite ECI; exact CINIT) ltac:((lazymatch goal with |- ?G => let G' := eval unfold um_st in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); rewrite Z.add_0_r; exact KC)).
      + exact HC0.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_free] in G in change_no_check G' end). exact NFH.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). lia.
      + intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & X3 & X4). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_fa] in G in change_no_check G' end). fold flo.
        split; [exact X4|]. split; [exact X2|]. split; [exact X3|]. unfold pop_zone_t in X1. fold r mu mfa ulo flo in X1.
        split; [intros Hin; apply X1; right; right; left; exact Hin|].
        intros RM. split; intros Hin; apply X1; do 3 right; (split; [exact RM|]); [left; exact Hin | right; exact Hin].
      + exact PR1. + exact A1. + exact A10. + exact A11. + exact A12.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_free] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end). fold nf. (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). exact A13.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_free] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end). fold nf. (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). exact A9.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). exact A19.
      + (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). exact A20.
      + exact A4. + exact A3. + exact Etp.
      + split; lia.
      + exact Hret.
      + exact SL1.
      + exact WST1.
      + intros fm r' M' mdl' NFT. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_fa] in G in change_no_check G' end). fold flo. intros W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 PRET.
        apply (CONT1 fm r' M' mdl' NFT W2 RX2 (same_except_vm_trans _ _ _ SEV1 SEV2)); [ | exact MW2 | exact HL2 | | exact PRET].
        * intros a Ha. rewrite (LK2 a Ha). exact (LK1 a Ha).
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold pop_foot, pop_zone_t in G in change_no_check G' end). fold r mu mfa ulo flo.
          destruct (decide (M' a = M1 a)) as [E | NE].
          -- rewrite E in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. split; [| exact Dd]. clear - F. lia.
          -- destruct (FOOT2 a NE) as [F Dd]. split; [| exact Dd]. clear - F. lia.
      + intros r' M' mdl' st'. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EREG. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_fa] in G in change_no_check G' end). fold flo. intros EST W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 PRET0.
        apply (CONT0 r' M' mdl' st' ltac:(destruct EST as [-> | [-> FT]]; [right; right; left; reflexivity | right; right; right; split; [reflexivity | exact FT]]) W2 RX2 (same_except_vm_trans _ _ _ SEV1 SEV2));
          [ | exact MW2 | exact HL2 | | exact PRET0].
        * intros a Ha. rewrite (LK2 a Ha). exact (LK1 a Ha).
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold pop_foot, pop_zone_t in G in change_no_check G' end). fold r mu mfa ulo flo.
          destruct (decide (M' a = M1 a)) as [E | NE].
          -- rewrite E in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. split; [clear - F; lia | left; exact Dd].
          -- destruct (FOOT2 a NE) as [[F Dd] | F]; [split; [clear - F; lia | left; exact Dd] | split; [unfold flo in *; clear - F MFA0; lia | right; unfold flo in *; clear - F MFA0; lia]].
    - (* [comment removed for export] *)
      intros r0 r' M' mdl' st'. fold r mu ulo. intros EST W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 AG (P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & PAG).
      apply (CONT0 r' M' mdl' st' ltac:(destruct EST as [-> | ->]; [left; reflexivity | right; left; reflexivity]) W2 RX2 SEV2 LK2 MW2 HL2);
        [ | (lazymatch goal with |- ?G => let G' := eval unfold pf_ret in G in change_no_check G' end); repeat (split; [assumption|]);
            split; [rewrite (PAG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi);
                    rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); exact H4
                   | rewrite (PAG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi);
                     rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); exact H3]].
      intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold pop_foot, pop_zone_t in G in change_no_check G' end). fold r mu mfa ulo flo. destruct (FOOT2 a Ha) as [[F Dd] | F]; [split; [clear - F; lia | left; exact Dd] | split; [clear - F; lia | right; clear - F; lia]]. }
  Qed.

  Theorem populateN_katwD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp : word) (req : Z) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cinit st = true -> a_kact st <= KCAP ->
    let r := a_reg st c in let au := r_alloc_user r in let mu := r_mapped_user r in let nf := Z.of_nat (length (r_free r)) in let mfa := r_mapped_fa r in
    a_cache st c = [] -> nf < cache_hint c ->
    (forall z, X z -> ~ pop_zone_t st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160) /\ ~ (reginfo bt c <= z < reginfo bt c + 128)) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 0x103f18 ->
    getr regs 11 = stats -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 (reginfo bt c) -> getr regs 14 = Z_to_bv 64 req ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    (CEIL + 512 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> (1 <= req /\ csize c * req <= 2 ^ 18) -> au + csize c * req <= mu ->
    writableZ ASEGS M (U sp - 512) (U sp) ->
    (forall (fm : bool) (r' : bvmap 5 word) (M' : mem) mdl',
        (fm = false -> ~ ftest st c) ->
        WF bt (pop_st st c false fm) Lc FF -> RepX bt (XL c) (pop_st st c false fm) Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> pop_foot st c (U sp) (U a) /\ M' a <> None) ->
        pf_ret sp ra s0v s1v s2v s3v s4v s5v s6v tp gp 1 r' ->
        katwD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ (st' = op_fhole st c /\ ftest st c)) ->
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> pop_foot st c (U sp) (U a) /\ (M' a <> None \/ pop_zone_t st c (U a))) ->
        pf_ret sp ra s0v s1v s2v s3v s4v s5v s6v tp gp 0 r' ->
        katD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x50dd4%bv : word) M rom) mdl) Qok Qf.
  Proof using N3FH N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp req Qok Qf Hc W RX HALT MW CINIT KC r au mu nf mfa HC0 NFH XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 Hsp Hret Hreq NOMAP WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    pose proof (csize_pos c Hc) as [CS1 CS2].
    set (ulo := region_beg SBEG c + mu). set (flo := fa_beg SBEG c + mfa).
    assert (MFA0 : 0 <= mfa) by (pose proof (region_facts bt st Lc FF W c Hc) as RF; cbn zeta in RF; fold r mfa in RF; destruct RF as (_ & _ & _ & _ & _ & E6 & _); lia).
    assert (CSBEG : In (0x103f38, 8%nat, SBEG) (bt_consts bt)).
    { pose proof CELLS as CREST. do 18 (destruct CREST as (_ & CREST)). destruct CREST as (A1 & _). exact A1. }
    apply (popAn_katwD bt BT_segs BT_ia X c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp req Qok Qf Hc W RX HALT CSBEG).
    - intros z Hz. destruct (XOFF z Hz) as (_ & X2 & _ & X4). split; [exact X4 | exact X2].
    - exact H1. - exact H2. - exact H4. - exact H3. - exact H10. - exact H11. - exact H12. - exact H13. - exact H14.
    - exact H8. - exact H9. - exact H18. - exact H19. - exact H20. - exact H21. - exact H22.
    - split; lia.
    - exact Hreq.
    - exact NOMAP.
    - intros i Hi. apply WSTK. lia.
    - intros r1 M1 mdl1 RX1 SBM1 MI1 FOOT1 SL1 PR1 A1 A10 A11 A12 A13 A9 A19 A20 A4 A3. fold r au mu nf in A13, A9, A19, A20.
      assert (WST1 : writableZ ASEGS M1 (U sp - 512) (U sp - 64)).
      { intros i Hi. apply (repx_wr (fun _ => True) M1 M (fun a Ha => conj I (proj2 (FOOT1 a Ha))) (U sp - 512) (U sp) ltac:(lia) ltac:(lia) WSTK). lia. }
      apply (popBC_katwD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3FH c st Lc FF M1 rom mdl1 r1 sp ra s0v s1v s2v s3v s4v s5v s6v tp gp Qok Qf
               Hc W RX1 (halted_sbm mdl mdl1 SBM1 HALT) (model_ivs_wf_sbm mdl mdl1 SBM1 MW) CINIT KC HC0 NFH ltac:(fold r au mu; clear - NOMAP Hreq CS1; nia)).
      + intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & X3 & X4). fold r mfa flo.
        split; [exact X4|]. split; [exact X2|]. split; [exact X3|]. unfold pop_zone_t in X1. fold r mu mfa ulo flo in X1.
        split; [intros Hin; apply X1; right; right; left; exact Hin|].
        intros RM. split; intros Hin; apply X1; do 3 right; (split; [exact RM|]); [left; exact Hin | right; exact Hin].
      + exact PR1. + exact A1. + exact A10. + exact A11. + exact A12. + exact A13. + exact A9. + exact A19. + exact A20. + exact A4. + exact A3. + exact Etp.
      + split; lia.
      + exact Hret.
      + exact SL1.
      + exact WST1.
      + intros fm r' M' mdl' NFT. fold r mfa flo. intros W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 PRET.
        apply (CONT1 fm r' M' mdl' NFT W2 RX2 (same_except_vm_trans _ _ _ (same_but_materialized_except_vm _ _ SBM1) SEV2)); [ | exact MW2 | exact HL2 | | exact PRET].
        * intros a Ha. rewrite (LK2 a Ha). exact (lazy_kept_sbm bt Lc FF mdl mdl1 SBM1 a Ha).
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold pop_foot, pop_zone_t in G in change_no_check G' end). fold r mu mfa ulo flo.
          destruct (decide (M' a = M1 a)) as [E | NE].
          -- rewrite E in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. split; [| exact Dd]. clear - F. lia.
          -- destruct (FOOT2 a NE) as [F Dd]. split; [| exact Dd]. clear - F. lia.
      + intros r' M' mdl' st'. fold r mfa flo. intros EST W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 PRET0.
        apply (CONT0 r' M' mdl' st' EST W2 RX2 (same_except_vm_trans _ _ _ (same_but_materialized_except_vm _ _ SBM1) SEV2));
          [ | exact MW2 | exact HL2 | | exact PRET0].
        * intros a Ha. rewrite (LK2 a Ha). exact (lazy_kept_sbm bt Lc FF mdl mdl1 SBM1 a Ha).
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold pop_foot, pop_zone_t in G in change_no_check G' end). fold r mu mfa ulo flo.
          destruct (decide (M' a = M1 a)) as [E | NE].
          -- rewrite E in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. split; [clear - F; lia | left; exact Dd].
          -- destruct (FOOT2 a NE) as [[F Dd] | F]; [split; [clear - F; lia | left; exact Dd] | split; [unfold flo in *; clear - F MFA0; lia | right; unfold flo in *; clear - F MFA0; lia]].
  Qed.
End L3.
End WithCeil.
End AsAllocM8Lf.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8Li.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8h OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Le AsAllocM8Lf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lh.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys7c.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).







Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  Hypothesis N3F : N3F_stmt bt.
  Hypothesis N3U : N3U_stmt bt.
  Hypothesis N3FH : AsKSys10.AsKSys7c.N3FH_stmt bt.     (* [comment removed for export] *)
  Hypothesis N3UH : AsKSys10.AsKSys7c.N3UH_stmt bt.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).
  #[local] Abbreviation IA := (bt_ia bt).

  Definition refill_foot (st : ast) (c : Z) (sp : Z) (z : Z) : Prop :=
    (sp - 672 <= z < sp) \/ pop_zone_t bt st c z \/ (T + T_PC + PC_SZ * c <= z < T + T_PC + PC_SZ * c + 80) \/ (T + 2792 <= z < T + 2888)
    \/ (reginfo bt c <= z < reginfo bt c + 128).

  (* [comment removed for export] *)
  Lemma pop_zone_lt : forall st Lc FF c z, WF bt st Lc FF -> 1 <= c <= 30 -> pop_zone bt st c z -> 0 < z < SBEG + KSPACE.
  Proof using.
    intros st Lc FF c z W Hc PZ. pose proof ceil_rng as CR.
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (_ & _ & _ & _ & S1 & S2 & S3).
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & Y3 & _).
    unfold pop_zone in PZ. cbv zeta in PZ. unfold KSPACE, PG, KUSERMAP, KFAMAP, KREGION_EXHAUST, AS_HEAPLO in *.
    set (ulo := region_beg SBEG c + r_mapped_user (a_reg st c)) in *. set (flo := fa_beg SBEG c + r_mapped_fa (a_reg st c)) in *.
    assert (EFAB : fa_beg SBEG c = SBEG + c * 2 ^ 32 + 3758096384) by ((lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); reflexivity).
    assert (ERB : region_beg SBEG c = SBEG + c * 2 ^ 32) by ((lazymatch goal with |- ?G => let G' := eval unfold region_beg, KREGION in G in change_no_check G' end); reflexivity).
    assert (U1 : SBEG <= ulo /\ ulo + 2 ^ 18 <= SBEG + 2 ^ 37) by ((lazymatch goal with |- ?G => let G' := eval unfold ulo in G in change_no_check G' end); rewrite ERB; lia).
    assert (F1 : SBEG <= flo /\ flo + 2 ^ 18 <= SBEG + 2 ^ 37) by ((lazymatch goal with |- ?G => let G' := eval unfold flo in G in change_no_check G' end); rewrite EFAB; lia).
    assert (QU : 17594333495296 <= ulo /\ ulo + 2 ^ 18 <= CEIL) by (clear - U1 S2 S3; lia).
    assert (QF : 17594333495296 <= flo /\ flo + 2 ^ 18 <= CEIL) by (clear - F1 S2 S3; lia).
    destruct (sh_band ulo (2 ^ 18) (proj1 QU) ltac:(clear; lia) (proj2 QU) ltac:(reflexivity)) as (A0 & A1 & _).
    destruct (sh_band flo (2 ^ 18) (proj1 QF) ltac:(clear; lia) (proj2 QF) ltac:(reflexivity)) as (B0 & B1 & _).
    unfold AS_GAPHI, AS_HEAPLO, sh_lo in *. rewrite EFAB in PZ. clear - PZ U1 F1 A0 A1 B0 B1 S1 S3 EFAB Hc.
    lia.
  Qed.
  Lemma pop_zone_t_lt : forall st Lc FF c z, WF bt st Lc FF -> 1 <= c <= 30 -> pop_zone_t bt st c z -> 0 < z < SBEG + KSPACE.
  Proof using.
    intros st Lc FF c z W Hc PZ. apply (pop_zone_lt st Lc FF c z W Hc). apply (pop_zone_t_sub bt); [| exact PZ].
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & MF0 & _). exact MF0.
  Qed.

  (* [comment removed for export] *)
  Lemma pop_st_facts : forall st c um fm,
    a_cinit (pop_st bt st c um fm) = a_cinit st /\ a_cache (pop_st bt st c um fm) = a_cache st
    /\ r_free (a_reg (pop_st bt st c um fm) c)
       = r_free (a_reg st c) ++ carve_list SBEG c (r_alloc_user (a_reg st c) / csize c)
                                  ((r_mapped_user (a_reg st c) + (if um then KUSERMAP else 0) - r_alloc_user (a_reg st c)) / csize c).
  Proof using.
    intros st c um fm. (lazymatch goal with |- ?G => let G' := eval unfold pop_st, bc_st in G in change_no_check G' end).
    set (s1 := if um then um_st bt st c else st).
    assert (F1 : a_cinit s1 = a_cinit st /\ a_cache s1 = a_cache st /\ r_free (a_reg s1 c) = r_free (a_reg st c)
                 /\ r_alloc_user (a_reg s1 c) = r_alloc_user (a_reg st c)
                 /\ r_mapped_user (a_reg s1 c) = r_mapped_user (a_reg st c) + (if um then KUSERMAP else 0)).
    { (lazymatch goal with |- ?G => let G' := eval unfold s1 in G in change_no_check G' end). destruct um; [| rewrite Z.add_0_r; repeat split; reflexivity].
      destruct (um_st_reg bt st c) as [ER EC]. rewrite ER. (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_alloc_user r_mapped_user] in G in change_no_check G' end). repeat split; first [reflexivity | exact EC]. }
    destruct F1 as (A1 & A2 & A3 & A4 & A5).
    set (s2 := if fm then add_meter (op_famap s1 c) 0 [(sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg s1 c)), sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg s1 c)) + KFAMAP / 8)] 0 else s1).
    assert (F2 : a_cinit s2 = a_cinit st /\ a_cache s2 = a_cache st /\ r_free (a_reg s2 c) = r_free (a_reg st c)
                 /\ r_alloc_user (a_reg s2 c) = r_alloc_user (a_reg st c)
                 /\ r_mapped_user (a_reg s2 c) = r_mapped_user (a_reg st c) + (if um then KUSERMAP else 0)).
    { (lazymatch goal with |- ?G => let G' := eval unfold s2 in G in change_no_check G' end). destruct fm; [| exact (conj A1 (conj A2 (conj A3 (conj A4 A5))))].
      destruct (famap_fields s1 c c) as (M1 & M2 & _ & M4 & _). destruct (famap_rest s1 c) as (N1 & N2 & _).
      change (a_reg (add_meter (op_famap s1 c) 0 _ 0)) with (a_reg (op_famap s1 c)).
      change (a_cinit (add_meter (op_famap s1 c) 0 _ 0)) with (a_cinit (op_famap s1 c)).
      change (a_cache (add_meter (op_famap s1 c) 0 _ 0)) with (a_cache (op_famap s1 c)).
      rewrite M1, M2, M4, N1, N2. exact (conj A1 (conj A2 (conj A3 (conj A4 A5)))). }
    destruct F2 as (B1 & B2 & B3 & B4 & B5).
    destruct (carve_fields SBEG s2 c c) as (_ & _ & _ & C4 & _). rewrite Z.eqb_refl in C4. destruct (carve_rest SBEG s2 c) as (D1 & D2 & _).
    split; [rewrite D1; exact B1|]. split; [rewrite D2; exact B2|].
    rewrite C4. (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). rewrite B3, B4, B5. reflexivity.
  Qed.

  Theorem refill_popM_katsD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cinit st = true -> a_cache st c = [] -> a_kact st <= KCAP -> mu_room st ->
    let r := a_reg st c in let au := r_alloc_user r in let mu := r_mapped_user r in let nf := Z.of_nat (length (r_free r)) in let mfa := r_mapped_fa r in
    let m := cache_hint c in
    nf < m -> mu < au + csize c * (m - nf) ->
    (forall z, X z -> ~ pop_zone_t bt st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 (T + T_PC) ->
    getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) -> getr regs 12 = Z_to_bv 64 0x103f18 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 672 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    writableZ ASEGS M (U spR - 672) (U spR) ->
    (forall (fm : bool) (r' : bvmap 5 word) (M' : mem) mdl',
        (fm = false -> ~ ftest (um_st bt st c) c) ->
        let st' := op_refill (pop_st bt st c true fm) c m in
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' -> a_cache st' c <> [] ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill_foot st c (U spR) (U a) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qok Qf) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ st' = op_uhole st c \/ st' = um_st bt st c \/ (st' = op_fhole (um_st bt st c) c /\ ftest (um_st bt st c) c)) ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill_foot st c (U spR) (U a) /\ (M' a <> None \/ pop_zone_t bt st c (U a))) ->
        getr r' 10 = Z_to_bv 64 0 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qf) ->
    katsD ASEGS (mkCfg (mkst regs (0x509cc%bv : word) M rom) mdl) Qok Qf.
  Proof using N3UH N3FH N3U N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs spR raR tp gp Qok Qf Hc W RX HALT MW CINIT HC0 KC MUR r au mu nf mfa m NF NEEDMAP XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof (csize_pos c Hc) as [CS1 CS2]. pose proof (hint_size_le c Hc) as HSZ. fold m in HSZ.
    assert (Hm : 1 <= m <= 8) by ((lazymatch goal with |- ?G => let G' := eval unfold m, cache_hint in G in change_no_check G' end); lia).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _). fold mu au nf mfa in E2, E3, E4, E6, E7, E8.
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & _ & _ & T4k & _ & _).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (_ & _ & TSP & _ & S1 & S2 & S3).
    unfold KSPACE, PG, AS_HEAPLO in *.
    set (RIz := reginfo bt c) in *. assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    set (spG := at_ spR (-32)). assert (UspG : U spG = U spR - 32) by ((lazymatch goal with |- ?G => let G' := eval unfold spG in G in change_no_check G' end); rewrite at_u by lia; lia).
    set (spP := at_ spG (-128)). assert (UspP : U spP = U spR - 160) by ((lazymatch goal with |- ?G => let G' := eval unfold spP in G in change_no_check G' end); rewrite at_u by (rewrite UspG; lia); rewrite UspG; lia).
    assert (PZB : forall z, pop_zone_t bt st c z -> 0 < z < SBEG + 2 ^ 37) by (intros z Hz; exact (pop_zone_t_lt st Lc FF c z W Hc Hz)).
    (* [comment removed for export] *)
    assert (GINVT : forall (M1 M2 : mem) s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11,
               gf_inv bt M1 c spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 ->
               (forall a : word, M2 a <> M1 a -> pop_foot bt st c (U spP) (U a)) ->
               gf_inv bt M2 c spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11).
    { intros M1 M2 s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 (LK1 & GS1 & RS1) FT.
      assert (SAME : forall x : word, (RIz <= U x < RIz + 8) \/ (U spR - 160 <= U x < U spR) -> M2 x = M1 x).
      { intros x Hx. destruct (decide (M2 x = M1 x)) as [E | NE]; [exact E|]. exfalso. destruct (FT x NE) as [F | [F | [F | F]]].
        - rewrite UspP in F. lia.
        - pose proof (PZB _ F). lia.
        - clear - F Hx TSP ERI Hc T2 CR SP1. lia.
        - fold RIz in F. lia. }
      split; [| split].
      - rewrite <- LK1. apply rdn_ext; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply SAME. fold RIz. left. lia.
      - intros k v Hin. rewrite <- (GS1 k v Hin). fold spG.
        assert (Kk : -104 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        apply rdn_ext; [rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by (rewrite UspG; lia). rewrite UspG in Hx. cbn in Hx. apply SAME. right. lia.
      - intros k v Hin. rewrite <- (RS1 k v Hin).
        assert (Kk : -24 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        apply rdn_ext; [rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply SAME. right. lia. }
    apply (refill_head_K bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X (fun cf => katsD ASEGS cf Qok Qf) (liftable_katsD Qok Qf)
             c st Lc FF M rom mdl regs spR raR tp gp Hc W RX HALT CINIT HC0 NF).
    - intros z Hz. destruct (XOFF z Hz) as (_ & X2 & _ & X4 & X5). exact (conj X4 (conj X2 X5)).
    - exact H1. - exact H2. - exact H4. - exact H3. - exact H10. - exact H11. - exact H12. - exact H13.
    - split; lia.
    - intros i Hi. apply WSTK. lia.
    - intros r1 M1 mdl1 RX1 SBM1 MI1 FOOT1 GINV1 GR1 B1 B10 B11 B12 B13 B14 B4 B3. fold r nf m RIz in GINV1, GR1, B13, B14.
      destruct GR1 as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22). fold spG spP in G2.
      assert (WST1 : writableZ ASEGS M1 (U spP - 512) (U spP)).
      { intros i Hi. rewrite UspP in Hi. apply (repx_wr (fun _ => True) M1 M (fun a Ha => conj I (proj2 (FOOT1 a Ha))) (U spR - 672) (U spR) ltac:(lia) ltac:(lia) WSTK). lia. }
      apply (populateM_katsD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3U N3FH N3UH c st Lc FF M1 rom mdl1 r1 spP (Z_to_bv 64 0x50d88)
               (Z_to_bv 64 RIz) (Z_to_bv 64 0x103f18) (Z_to_bv 64 (RIz + 8)) (Z_to_bv 64 (2 ^ 61)) (Z_to_bv 64 (SBEG + c * 2 ^ 32 + 0xE0000000))
               (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16)) (Z_to_bv 64 m) tp gp (m - nf) Qok Qf
               Hc W RX1 (halted_sbm mdl mdl1 SBM1 HALT) (model_ivs_wf_sbm mdl mdl1 SBM1 MW) CINIT KC MUR HC0 NF).
      + intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & X3 & X4 & _). exact (conj X1 (conj X2 (conj X3 X4))).
      + exact B1. + exact G2. + exact B4. + exact B3. + exact Etp. + exact B10. + exact B11. + exact B12. + exact B13. + exact B14.
      + exact G8. + exact G9. + exact G18. + exact G19. + exact G20. + exact G21. + exact G22.
      + rewrite UspP. split; lia.
      + apply ret_ok_lit; [lia | reflexivity].
      + split; [lia|]. fold r au mu in NEEDMAP. clear - HSZ Hm NF E7 CS1. nia.
      + exact NEEDMAP.
      + exact WST1.
      + (* [comment removed for export] *)
        intros fm r2 M2 mdl2 NFT W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 (P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P4 & P3).
        set (st2 := pop_st bt st c true fm) in *.
        destruct (pop_st_facts st c true fm) as (F_ci & F_ca & F_fr). fold st2 r au mu in F_ci, F_ca, F_fr.
        set (newn := (mu + KUSERMAP - au) / csize c) in *.
        assert (N0 : m - nf <= newn).
        { (lazymatch goal with |- ?G => let G' := eval unfold newn in G in change_no_check G' end). apply Z.div_le_lower_bound; [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). clear - HSZ Hm NF E7 CS1 E3. nia. }
        assert (LEN2 : Z.of_nat (length (r_free (a_reg st2 c))) = nf + newn).
        { rewrite F_fr, length_app, Nat2Z.inj_add. fold nf. rewrite (carve_list_length bt c _ newn ltac:(lia)). reflexivity. }
        replace (Z_to_bv 64 0x50d88 : word) with (0x50d88%bv : word) by (apply bv_eq; reflexivity).
        apply (refill_ok_K bt BT_segs BT_ia X (fun cf => katwD ASEGS cf Qok Qf) (liftable_katwD Qok Qf) c st2 Lc FF M2 rom mdl2 r2 spR raR (getr regs 8) (getr regs 9)
                 (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
                 Hc W2 RX2 HL2 ltac:(rewrite F_ci; exact CINIT) ltac:(rewrite F_ca; exact HC0)).
        * fold m. rewrite LEN2. lia.
        * intros z Hz. destruct (XOFF z Hz) as (X1 & _ & _ & X4 & X5). split; [exact X4|]. split; [| exact X5].
          rewrite LEN2. intros Hin. apply X1. (lazymatch goal with |- ?G => let G' := eval unfold pop_zone_t in G in change_no_check G' end). fold r mu mfa. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end).
          (* [comment removed for export] *)
          pose proof W2 as ((WR2 & _) & _). destruct (WR2 c Hc) as (_ & _ & _ & _ & _ & _ & Y7 & Y8 & _). rewrite LEN2 in Y7.
          assert (MFA2 : r_mapped_fa (a_reg st2 c) = mfa \/ r_mapped_fa (a_reg st2 c) = mfa + 2 ^ 18).
          { (lazymatch goal with |- ?G => let G' := eval unfold st2, pop_st, bc_st in G in change_no_check G' end). destruct (carve_fields SBEG (if fm then add_meter (op_famap (um_st bt st c) c) 0 [(sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg (um_st bt st c) c)), sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg (um_st bt st c) c)) + KFAMAP / 8)] 0 else um_st bt st c) c c) as (_ & _ & C3 & _).
            rewrite C3. destruct (um_st_reg bt st c) as [ER _]. destruct fm.
            - right. change (a_reg (add_meter (op_famap (um_st bt st c) c) 0 _ 0)) with (a_reg (op_famap (um_st bt st c) c)).
              destruct (famap_fields (um_st bt st c) c c) as (_ & _ & M3 & _). rewrite Z.eqb_refl in M3. rewrite M3, ER. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_fa] in G in change_no_check G' end). fold r mfa. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). lia.
            - left. rewrite ER. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_fa] in G in change_no_check G' end). fold r mfa. lia. }
          destruct (Z_lt_le_dec z (fa_beg SBEG c + mfa)) as [Lz | Lz]; [right; right; left; clear - Hin Lz; lia|].
          do 3 right. split; [clear - Hin Y7 Y8 MFA2 Lz; lia | left; clear - Hin Y7 MFA2 Lz; lia].
        * fold m. exact (GINVT M1 M2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GINV1 (fun a Ha => proj1 (FOOT2 a Ha))).
        * fold m RIz. (lazymatch goal with |- ?G => let G' := eval unfold gfp_regs in G in change_no_check G' end). fold spG spP. repeat split; assumption.
        * exact P10.
        * split; lia.
        * exact HretR.
        * intros r3 M3 mdl3 W3 RX3 SBM3 MI3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3. fold m in W3, RX3.
          assert (CNE : a_cache (op_refill st2 c m) c <> []) by (apply refill_cache_ne; rewrite LEN2; lia).
          apply (CONT1 fm r3 M3 mdl3 NFT W3 RX3 CNE).
          -- eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1|]. eapply same_except_vm_trans; [exact SEV2 | apply same_but_materialized_except_vm; exact SBM3].
          -- intros a Ha. rewrite (lazy_kept_sbm bt Lc FF mdl2 mdl3 SBM3 a Ha). rewrite (LK2 a Ha). exact (lazy_kept_sbm bt Lc FF mdl mdl1 SBM1 a Ha).
          -- exact (model_ivs_wf_sbm mdl2 mdl3 SBM3 MW2).
          -- exact (halted_sbm mdl2 mdl3 SBM3 HL2).
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end). fold RIz.
             destruct (decide (M3 a = M2 a)) as [E3' | NE3].
             ++ rewrite E3' in Ha |- *. destruct (decide (M2 a = M1 a)) as [E2' | NE2].
                ** rewrite E2' in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. split; [| exact Dd]. fold RIz in F. clear - F. lia.
                ** destruct (FOOT2 a NE2) as [F Dd]. split; [| exact Dd]. unfold pop_foot in F. rewrite UspP in F. fold RIz in F.
                   destruct F as [F | [F | [F | F]]]; [left; clear - F; lia | right; left; exact F | right; right; right; left; exact F | right; right; right; right; clear - F; lia].
             ++ destruct (FOOT3 a NE3) as [F Dd]. split; [| exact Dd]. fold RIz in F. clear - F. lia.
          -- exact Q10. -- exact Q2. -- exact Q1. -- exact Q8. -- exact Q9. -- exact QS. -- rewrite Q4. exact P4. -- rewrite Q3. exact P3.
      + (* [comment removed for export] *)
        intros r2 M2 mdl2 st2 EST W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 (P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P4 & P3).
        replace (Z_to_bv 64 0x50d88 : word) with (0x50d88%bv : word) by (apply bv_eq; reflexivity).
        apply (refill_fail_K bt BT_segs BT_ia X (fun cf => katD ASEGS cf Qf) (liftable_katD Qf) c st2 Lc FF M2 rom mdl2 r2 spR raR (getr regs 8) (getr regs 9)
                 (Z_to_bv 64 (T + T_PC + PC_SZ * c)) (Z_to_bv 64 m)
                 (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
                 Hc W2 RX2 HL2).
        * intros z Hz Hin. destruct (XOFF z Hz) as (_ & _ & _ & X4 & _). apply X4. lia.
        * exact (GINVT M1 M2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GINV1 (fun a Ha => proj1 (FOOT2 a Ha))).
        * exact P2.
        * fold RIz. exact P8.
        * exact P19.
        * exact P10.
        * split; lia.
        * exact HretR.
        * intros r3 M3 mdl3 RX3 SBM3 MI3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
          apply (CONT0 r3 M3 mdl3 st2 EST W2 RX3).
          -- eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1|]. eapply same_except_vm_trans; [exact SEV2 | apply same_but_materialized_except_vm; exact SBM3].
          -- intros a Ha. rewrite (lazy_kept_sbm bt Lc FF mdl2 mdl3 SBM3 a Ha). rewrite (LK2 a Ha). exact (lazy_kept_sbm bt Lc FF mdl mdl1 SBM1 a Ha).
          -- exact (model_ivs_wf_sbm mdl2 mdl3 SBM3 MW2).
          -- exact (halted_sbm mdl2 mdl3 SBM3 HL2).
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end). fold RIz.
             destruct (decide (M3 a = M2 a)) as [E3' | NE3].
             ++ rewrite E3' in Ha |- *. destruct (decide (M2 a = M1 a)) as [E2' | NE2].
                ** rewrite E2' in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. fold RIz in F. split; [clear - F; lia | left; exact Dd].
                ** destruct (FOOT2 a NE2) as [F DZ]. unfold pop_foot in F. rewrite UspP in F. fold RIz in F. split; [| exact DZ].
                   destruct F as [F | [F | [F | F]]]; [left; clear - F; lia | right; left; exact F | right; right; right; left; exact F | right; right; right; right; clear - F; lia].
             ++ destruct (FOOT3 a NE3) as [F Dd]. fold RIz in F. split; [clear - F; lia | left; exact Dd].
          -- exact Q10. -- exact Q2. -- exact Q1. -- exact Q8. -- exact Q9. -- exact QS.
          -- rewrite Q4. exact P4.
          -- rewrite Q3. exact P3.
  Qed.

  Theorem refill_popN_katwD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cinit st = true -> a_cache st c = [] -> a_kact st <= KCAP ->
    let r := a_reg st c in let au := r_alloc_user r in let mu := r_mapped_user r in let nf := Z.of_nat (length (r_free r)) in let mfa := r_mapped_fa r in
    let m := cache_hint c in
    nf < m -> au + csize c * (m - nf) <= mu ->
    (forall z, X z -> ~ pop_zone_t bt st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 (T + T_PC) ->
    getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) -> getr regs 12 = Z_to_bv 64 0x103f18 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 672 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    writableZ ASEGS M (U spR - 672) (U spR) ->
    (forall (fm : bool) (r' : bvmap 5 word) (M' : mem) mdl',
        (fm = false -> ~ ftest st c) ->
        let st' := op_refill (pop_st bt st c false fm) c m in
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' -> a_cache st' c <> [] ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill_foot st c (U spR) (U a) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qok Qf) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ (st' = op_fhole st c /\ ftest st c)) ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill_foot st c (U spR) (U a) /\ (M' a <> None \/ pop_zone_t bt st c (U a))) ->
        getr r' 10 = Z_to_bv 64 0 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x509cc%bv : word) M rom) mdl) Qok Qf.
  Proof using N3FH N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs spR raR tp gp Qok Qf Hc W RX HALT MW CINIT HC0 KC r au mu nf mfa m NF NOMAP XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof (csize_pos c Hc) as [CS1 CS2]. pose proof (hint_size_le c Hc) as HSZ. fold m in HSZ.
    assert (Hm : 1 <= m <= 8) by ((lazymatch goal with |- ?G => let G' := eval unfold m, cache_hint in G in change_no_check G' end); lia).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _). fold mu au nf mfa in E2, E3, E4, E6, E7, E8.
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & _ & _ & T4k & _ & _).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (_ & _ & TSP & _ & S1 & S2 & S3).
    unfold KSPACE, PG, AS_HEAPLO in *.
    set (RIz := reginfo bt c) in *. assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    set (spG := at_ spR (-32)). assert (UspG : U spG = U spR - 32) by ((lazymatch goal with |- ?G => let G' := eval unfold spG in G in change_no_check G' end); rewrite at_u by lia; lia).
    set (spP := at_ spG (-128)). assert (UspP : U spP = U spR - 160) by ((lazymatch goal with |- ?G => let G' := eval unfold spP in G in change_no_check G' end); rewrite at_u by (rewrite UspG; lia); rewrite UspG; lia).
    assert (PZB : forall z, pop_zone_t bt st c z -> 0 < z < SBEG + 2 ^ 37) by (intros z Hz; exact (pop_zone_t_lt st Lc FF c z W Hc Hz)).
    (* [comment removed for export] *)
    assert (GINVT : forall (M1 M2 : mem) s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11,
               gf_inv bt M1 c spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 ->
               (forall a : word, M2 a <> M1 a -> pop_foot bt st c (U spP) (U a)) ->
               gf_inv bt M2 c spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11).
    { intros M1 M2 s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 (LK1 & GS1 & RS1) FT.
      assert (SAME : forall x : word, (RIz <= U x < RIz + 8) \/ (U spR - 160 <= U x < U spR) -> M2 x = M1 x).
      { intros x Hx. destruct (decide (M2 x = M1 x)) as [E | NE]; [exact E|]. exfalso. destruct (FT x NE) as [F | [F | [F | F]]].
        - rewrite UspP in F. lia.
        - pose proof (PZB _ F). lia.
        - clear - F Hx TSP ERI Hc T2 CR SP1. lia.
        - fold RIz in F. lia. }
      split; [| split].
      - rewrite <- LK1. apply rdn_ext; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply SAME. fold RIz. left. lia.
      - intros k v Hin. rewrite <- (GS1 k v Hin). fold spG.
        assert (Kk : -104 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        apply rdn_ext; [rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by (rewrite UspG; lia). rewrite UspG in Hx. cbn in Hx. apply SAME. right. lia.
      - intros k v Hin. rewrite <- (RS1 k v Hin).
        assert (Kk : -24 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        apply rdn_ext; [rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply SAME. right. lia. }
    apply (refill_head_K bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X (fun cf => katwD ASEGS cf Qok Qf) (liftable_katwD Qok Qf)
             c st Lc FF M rom mdl regs spR raR tp gp Hc W RX HALT CINIT HC0 NF).
    - intros z Hz. destruct (XOFF z Hz) as (_ & X2 & _ & X4 & X5). exact (conj X4 (conj X2 X5)).
    - exact H1. - exact H2. - exact H4. - exact H3. - exact H10. - exact H11. - exact H12. - exact H13.
    - split; lia.
    - intros i Hi. apply WSTK. lia.
    - intros r1 M1 mdl1 RX1 SBM1 MI1 FOOT1 GINV1 GR1 B1 B10 B11 B12 B13 B14 B4 B3. fold r nf m RIz in GINV1, GR1, B13, B14.
      destruct GR1 as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22). fold spG spP in G2.
      assert (WST1 : writableZ ASEGS M1 (U spP - 512) (U spP)).
      { intros i Hi. rewrite UspP in Hi. apply (repx_wr (fun _ => True) M1 M (fun a Ha => conj I (proj2 (FOOT1 a Ha))) (U spR - 672) (U spR) ltac:(lia) ltac:(lia) WSTK). lia. }
      apply (populateN_katwD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3FH c st Lc FF M1 rom mdl1 r1 spP (Z_to_bv 64 0x50d88)
               (Z_to_bv 64 RIz) (Z_to_bv 64 0x103f18) (Z_to_bv 64 (RIz + 8)) (Z_to_bv 64 (2 ^ 61)) (Z_to_bv 64 (SBEG + c * 2 ^ 32 + 0xE0000000))
               (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16)) (Z_to_bv 64 m) (at_ (Z_to_bv 64 T) 2768) tp gp (m - nf) Qok Qf
               Hc W RX1 (halted_sbm mdl mdl1 SBM1 HALT) (model_ivs_wf_sbm mdl mdl1 SBM1 MW) CINIT KC HC0 NF).
      + intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & X3 & X4 & _). exact (conj X1 (conj X2 (conj X3 X4))).
      + exact B1. + exact G2. + exact B4. + exact B3. + exact Etp. + exact B10. + exact B11. + exact B12. + exact B13. + exact B14.
      + exact G8. + exact G9. + exact G18. + exact G19. + exact G20. + exact G21. + exact G22.
      + rewrite UspP. split; lia.
      + apply ret_ok_lit; [lia | reflexivity].
      + split; [lia|]. clear - HSZ Hm NF E7 CS1. nia.
      + exact NOMAP.
      + exact WST1.
      + (* [comment removed for export] *)
        intros fm r2 M2 mdl2 NFT W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 (P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P4 & P3).
        set (st2 := pop_st bt st c false fm) in *.
        destruct (pop_st_facts st c false fm) as (F_ci & F_ca & F_fr). fold st2 r au mu in F_ci, F_ca, F_fr. rewrite Z.add_0_r in F_fr.
        set (newn := (mu - au) / csize c) in *.
        assert (N0 : m - nf <= newn).
        { (lazymatch goal with |- ?G => let G' := eval unfold newn in G in change_no_check G' end). apply Z.div_le_lower_bound; [lia|]. clear - NOMAP. lia. }
        assert (LEN2 : Z.of_nat (length (r_free (a_reg st2 c))) = nf + newn).
        { rewrite F_fr, length_app, Nat2Z.inj_add. fold nf. rewrite (carve_list_length bt c _ newn ltac:(lia)). reflexivity. }
        replace (Z_to_bv 64 0x50d88 : word) with (0x50d88%bv : word) by (apply bv_eq; reflexivity).
        apply (refill_ok_K bt BT_segs BT_ia X (fun cf => katwD ASEGS cf Qok Qf) (liftable_katwD Qok Qf) c st2 Lc FF M2 rom mdl2 r2 spR raR (getr regs 8) (getr regs 9)
                 (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
                 Hc W2 RX2 HL2 ltac:(rewrite F_ci; exact CINIT) ltac:(rewrite F_ca; exact HC0)).
        * fold m. rewrite LEN2. lia.
        * intros z Hz. destruct (XOFF z Hz) as (X1 & _ & _ & X4 & X5). split; [exact X4|]. split; [| exact X5].
          rewrite LEN2. intros Hin. apply X1. (lazymatch goal with |- ?G => let G' := eval unfold pop_zone_t in G in change_no_check G' end). fold r mu mfa. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end).
          (* [comment removed for export] *)
          pose proof W2 as ((WR2 & _) & _). destruct (WR2 c Hc) as (_ & _ & _ & _ & _ & _ & Y7 & Y8 & _). rewrite LEN2 in Y7.
          assert (MFA2 : r_mapped_fa (a_reg st2 c) = mfa \/ r_mapped_fa (a_reg st2 c) = mfa + 2 ^ 18).
          { (lazymatch goal with |- ?G => let G' := eval unfold st2, pop_st, bc_st in G in change_no_check G' end). destruct (carve_fields SBEG (if fm then add_meter (op_famap st c) 0 [(sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg st c)), sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg st c)) + KFAMAP / 8)] 0 else st) c c) as (_ & _ & C3 & _).
            rewrite C3. destruct fm.
            - right. change (a_reg (add_meter (op_famap st c) 0 _ 0)) with (a_reg (op_famap st c)).
              destruct (famap_fields st c c) as (_ & _ & M3 & _). rewrite Z.eqb_refl in M3. rewrite M3. fold r mfa. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). lia.
            - left. fold r mfa. lia. }
          destruct (Z_lt_le_dec z (fa_beg SBEG c + mfa)) as [Lz | Lz]; [right; right; left; clear - Hin Lz; lia|].
          do 3 right. split; [clear - Hin Y7 Y8 MFA2 Lz; lia | left; clear - Hin Y7 MFA2 Lz; lia].
        * fold m. exact (GINVT M1 M2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GINV1 (fun a Ha => proj1 (FOOT2 a Ha))).
        * fold m RIz. (lazymatch goal with |- ?G => let G' := eval unfold gfp_regs in G in change_no_check G' end). fold spG spP. repeat split; assumption.
        * exact P10.
        * split; lia.
        * exact HretR.
        * intros r3 M3 mdl3 W3 RX3 SBM3 MI3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3. fold m in W3, RX3.
          assert (CNE : a_cache (op_refill st2 c m) c <> []) by (apply refill_cache_ne; rewrite LEN2; lia).
          apply (CONT1 fm r3 M3 mdl3 NFT W3 RX3 CNE).
          -- eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1|]. eapply same_except_vm_trans; [exact SEV2 | apply same_but_materialized_except_vm; exact SBM3].
          -- intros a Ha. rewrite (lazy_kept_sbm bt Lc FF mdl2 mdl3 SBM3 a Ha). rewrite (LK2 a Ha). exact (lazy_kept_sbm bt Lc FF mdl mdl1 SBM1 a Ha).
          -- exact (model_ivs_wf_sbm mdl2 mdl3 SBM3 MW2).
          -- exact (halted_sbm mdl2 mdl3 SBM3 HL2).
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end). fold RIz.
             destruct (decide (M3 a = M2 a)) as [E3' | NE3].
             ++ rewrite E3' in Ha |- *. destruct (decide (M2 a = M1 a)) as [E2' | NE2].
                ** rewrite E2' in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. split; [| exact Dd]. fold RIz in F. clear - F. lia.
                ** destruct (FOOT2 a NE2) as [F Dd]. split; [| exact Dd]. unfold pop_foot in F. rewrite UspP in F. fold RIz in F.
                   destruct F as [F | [F | [F | F]]]; [left; clear - F; lia | right; left; exact F | right; right; right; left; exact F | right; right; right; right; clear - F; lia].
             ++ destruct (FOOT3 a NE3) as [F Dd]. split; [| exact Dd]. fold RIz in F. clear - F. lia.
          -- exact Q10. -- exact Q2. -- exact Q1. -- exact Q8. -- exact Q9. -- exact QS. -- rewrite Q4. exact P4. -- rewrite Q3. exact P3.
      + (* [comment removed for export] *)
        intros r2 M2 mdl2 st2 EST W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 (P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P4 & P3).
        replace (Z_to_bv 64 0x50d88 : word) with (0x50d88%bv : word) by (apply bv_eq; reflexivity).
        apply (refill_fail_K bt BT_segs BT_ia X (fun cf => katD ASEGS cf Qf) (liftable_katD Qf) c st2 Lc FF M2 rom mdl2 r2 spR raR (getr regs 8) (getr regs 9)
                 (Z_to_bv 64 (T + T_PC + PC_SZ * c)) (Z_to_bv 64 m)
                 (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
                 Hc W2 RX2 HL2).
        * intros z Hz Hin. destruct (XOFF z Hz) as (_ & _ & _ & X4 & _). apply X4. lia.
        * exact (GINVT M1 M2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GINV1 (fun a Ha => proj1 (FOOT2 a Ha))).
        * exact P2.
        * fold RIz. exact P8.
        * exact P19.
        * exact P10.
        * split; lia.
        * exact HretR.
        * intros r3 M3 mdl3 RX3 SBM3 MI3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
          apply (CONT0 r3 M3 mdl3 st2 EST W2 RX3).
          -- eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1|]. eapply same_except_vm_trans; [exact SEV2 | apply same_but_materialized_except_vm; exact SBM3].
          -- intros a Ha. rewrite (lazy_kept_sbm bt Lc FF mdl2 mdl3 SBM3 a Ha). rewrite (LK2 a Ha). exact (lazy_kept_sbm bt Lc FF mdl mdl1 SBM1 a Ha).
          -- exact (model_ivs_wf_sbm mdl2 mdl3 SBM3 MW2).
          -- exact (halted_sbm mdl2 mdl3 SBM3 HL2).
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end). fold RIz.
             destruct (decide (M3 a = M2 a)) as [E3' | NE3].
             ++ rewrite E3' in Ha |- *. destruct (decide (M2 a = M1 a)) as [E2' | NE2].
                ** rewrite E2' in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. fold RIz in F. split; [clear - F; lia | left; exact Dd].
                ** destruct (FOOT2 a NE2) as [F DZ]. unfold pop_foot in F. rewrite UspP in F. fold RIz in F. split; [| exact DZ].
                   destruct F as [F | [F | [F | F]]]; [left; clear - F; lia | right; left; exact F | right; right; right; left; exact F | right; right; right; right; clear - F; lia].
             ++ destruct (FOOT3 a NE3) as [F Dd]. fold RIz in F. split; [clear - F; lia | left; exact Dd].
          -- exact Q10. -- exact Q2. -- exact Q1. -- exact Q8. -- exact Q9. -- exact QS.
          -- rewrite Q4. exact P4.
          -- rewrite Q3. exact P3.
  Qed.
End L3.
End WithCeil.
End AsAllocM8Li.
Module AsAllocM8Lj.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8h OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Le AsAllocM8Lf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lh.
Import AsAllocM8Li.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys7c.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).







Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  Hypothesis N3F : N3F_stmt bt.
  Hypothesis N3U : N3U_stmt bt.
  Hypothesis N3FH : AsKSys10.AsKSys7c.N3FH_stmt bt.     (* [comment removed for export] *)
  Hypothesis N3UH : AsKSys10.AsKSys7c.N3UH_stmt bt.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).
  #[local] Abbreviation IA := (bt_ia bt).

  Theorem refill_popM_tail :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp s0R s1R g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cinit st = true -> a_cache st c = [] -> a_kact st <= KCAP -> mu_room st ->
    let r := a_reg st c in let au := r_alloc_user r in let mu := r_mapped_user r in let nf := Z.of_nat (length (r_free r)) in let mfa := r_mapped_fa r in
    let m := cache_hint c in
    nf < m -> mu < au + csize c * (m - nf) ->
    (forall z, X z -> ~ pop_zone_t bt st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (T <= z < T + 2768)) ->
    U tp = TP ->
    (CEIL + 672 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    writableZ ASEGS M (U spR - 672) (U spR - 160) ->
    gf_inv bt M c spR raR s0R s1R (Z_to_bv 64 0x50a0c) (Z_to_bv 64 (T + T_PC + PC_SZ * c)) (Z_to_bv 64 m) g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 ->
    gfp_regs (at_ spR (-32)) (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16)) (reginfo bt c) SBEG c m regs ->
    getr regs 1 = Z_to_bv 64 0x50d88 -> getr regs 10 = Z_to_bv 64 0x103f18 -> getr regs 11 = at_ (Z_to_bv 64 T) 2768 -> getr regs 12 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 (reginfo bt c) -> getr regs 14 = Z_to_bv 64 (m - nf) -> getr regs 4 = tp -> getr regs 3 = gp ->
    (forall (fm : bool) (r' : bvmap 5 word) (M' : mem) mdl',
        (fm = false -> ~ ftest (um_st bt st c) c) ->
        let st' := op_refill (pop_st bt st c true fm) c m in
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' -> a_cache st' c <> [] ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill_foot bt st c (U spR) (U a) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = s0R -> getr r' 9 = s1R -> s_regs r' g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qok Qf) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ st' = op_uhole st c \/ st' = um_st bt st c \/ (st' = op_fhole (um_st bt st c) c /\ ftest (um_st bt st c) c)) ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill_foot bt st c (U spR) (U a) /\ (M' a <> None \/ pop_zone_t bt st c (U a))) ->
        getr r' 10 = Z_to_bv 64 0 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = s0R -> getr r' 9 = s1R -> s_regs r' g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 -> getr r' 4 = tp -> getr r' 3 = gp ->
        katD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qf) ->
    katsD ASEGS (mkCfg (mkst regs (0x50dd4%bv : word) M rom) mdl) Qok Qf.
  Proof using N3UH N3FH N3U N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs spR raR tp gp s0R s1R g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 Qok Qf Hc W RX HALT MW CINIT HC0 KC MUR r au mu nf mfa m NF NEEDMAP XOFF
           Etp Hsp HretR WSTK GINV1 GR1 B1 B10 B11 B12 B13 B14 B4 B3 CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof (csize_pos c Hc) as [CS1 CS2]. pose proof (hint_size_le c Hc) as HSZ. fold m in HSZ.
    assert (Hm : 1 <= m <= 8) by ((lazymatch goal with |- ?G => let G' := eval unfold m, cache_hint in G in change_no_check G' end); lia).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _). fold mu au nf mfa in E2, E3, E4, E6, E7, E8.
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & _ & _ & T4k & _ & _).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (_ & _ & TSP & _ & S1 & S2 & S3).
    unfold KSPACE, PG, AS_HEAPLO in *.
    set (RIz := reginfo bt c) in *. assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    set (spG := at_ spR (-32)). assert (UspG : U spG = U spR - 32) by ((lazymatch goal with |- ?G => let G' := eval unfold spG in G in change_no_check G' end); rewrite at_u by lia; lia).
    set (spP := at_ spG (-128)). assert (UspP : U spP = U spR - 160) by ((lazymatch goal with |- ?G => let G' := eval unfold spP in G in change_no_check G' end); rewrite at_u by (rewrite UspG; lia); rewrite UspG; lia).
    assert (PZB : forall z, pop_zone_t bt st c z -> 0 < z < SBEG + 2 ^ 37) by (intros z Hz; exact (pop_zone_t_lt bt st Lc FF c z W Hc Hz)).
    (* [comment removed for export] *)
    assert (GINVT : forall (M1 M2 : mem) y0R y1R y_ra y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11,
               gf_inv bt M1 c spR raR y0R y1R y_ra y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 ->
               (forall a : word, M2 a <> M1 a -> pop_foot bt st c (U spP) (U a)) ->
               gf_inv bt M2 c spR raR y0R y1R y_ra y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11).
    { intros M1 M2 y0R y1R y_ra y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 (LK1 & GS1 & RS1) FT.
      assert (SAME : forall x : word, (RIz <= U x < RIz + 8) \/ (U spR - 160 <= U x < U spR) -> M2 x = M1 x).
      { intros x Hx. destruct (decide (M2 x = M1 x)) as [E | NE]; [exact E|]. exfalso. destruct (FT x NE) as [F | [F | [F | F]]].
        - rewrite UspP in F. lia.
        - pose proof (PZB _ F). lia.
        - clear - F Hx TSP ERI Hc T2 CR SP1. lia.
        - fold RIz in F. lia. }
      split; [| split].
      - rewrite <- LK1. apply rdn_ext; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply SAME. fold RIz. left. lia.
      - intros k v Hin. rewrite <- (GS1 k v Hin). fold spG.
        assert (Kk : -104 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        apply rdn_ext; [rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by (rewrite UspG; lia). rewrite UspG in Hx. cbn in Hx. apply SAME. right. lia.
      - intros k v Hin. rewrite <- (RS1 k v Hin).
        assert (Kk : -24 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        apply rdn_ext; [rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply SAME. right. lia. }
    fold r nf m RIz in GINV1, GR1, B13, B14.
      destruct GR1 as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22). fold spG spP in G2.
      assert (WST1 : writableZ ASEGS M (U spP - 512) (U spP)).
      { intros i Hi. rewrite UspP in Hi. apply WSTK. lia. }
      apply (populateM_katsD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3U N3FH N3UH c st Lc FF M rom mdl regs spP (Z_to_bv 64 0x50d88)
               (Z_to_bv 64 RIz) (Z_to_bv 64 0x103f18) (Z_to_bv 64 (RIz + 8)) (Z_to_bv 64 (2 ^ 61)) (Z_to_bv 64 (SBEG + c * 2 ^ 32 + 0xE0000000))
               (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16)) (Z_to_bv 64 m) tp gp (m - nf) Qok Qf
               Hc W RX HALT MW CINIT KC MUR HC0 NF).
      + intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & X3 & X4 & _). exact (conj X1 (conj X2 (conj X3 X4))).
      + exact B1. + exact G2. + exact B4. + exact B3. + exact Etp. + exact B10. + exact B11. + exact B12. + exact B13. + exact B14.
      + exact G8. + exact G9. + exact G18. + exact G19. + exact G20. + exact G21. + exact G22.
      + rewrite UspP. split; lia.
      + apply ret_ok_lit; [lia | reflexivity].
      + split; [lia|]. fold r au mu in NEEDMAP. clear - HSZ Hm NF E7 CS1. nia.
      + exact NEEDMAP.
      + exact WST1.
      + (* [comment removed for export] *)
        intros fm r2 M2 mdl2 NFT W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 (P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P4 & P3).
        set (st2 := pop_st bt st c true fm) in *.
        destruct (pop_st_facts bt st c true fm) as (F_ci & F_ca & F_fr). fold st2 r au mu in F_ci, F_ca, F_fr.
        set (newn := (mu + KUSERMAP - au) / csize c) in *.
        assert (N0 : m - nf <= newn).
        { (lazymatch goal with |- ?G => let G' := eval unfold newn in G in change_no_check G' end). apply Z.div_le_lower_bound; [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). clear - HSZ Hm NF E7 CS1 E3. nia. }
        assert (LEN2 : Z.of_nat (length (r_free (a_reg st2 c))) = nf + newn).
        { rewrite F_fr, length_app, Nat2Z.inj_add. fold nf. rewrite (carve_list_length bt c _ newn ltac:(lia)). reflexivity. }
        replace (Z_to_bv 64 0x50d88 : word) with (0x50d88%bv : word) by (apply bv_eq; reflexivity).
        apply (refill_ok_K bt BT_segs BT_ia X (fun cf => katwD ASEGS cf Qok Qf) (liftable_katwD Qok Qf) c st2 Lc FF M2 rom mdl2 r2 spR raR s0R s1R
                 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
                 Hc W2 RX2 HL2 ltac:(rewrite F_ci; exact CINIT) ltac:(rewrite F_ca; exact HC0)).
        * fold m. rewrite LEN2. lia.
        * intros z Hz. destruct (XOFF z Hz) as (X1 & _ & _ & X4 & X5). split; [exact X4|]. split; [| exact X5].
          rewrite LEN2. intros Hin. apply X1. (lazymatch goal with |- ?G => let G' := eval unfold pop_zone_t in G in change_no_check G' end). fold r mu mfa. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end).
          (* [comment removed for export] *)
          pose proof W2 as ((WR2 & _) & _). destruct (WR2 c Hc) as (_ & _ & _ & _ & _ & _ & Y7 & Y8 & _). rewrite LEN2 in Y7.
          assert (MFA2 : r_mapped_fa (a_reg st2 c) = mfa \/ r_mapped_fa (a_reg st2 c) = mfa + 2 ^ 18).
          { (lazymatch goal with |- ?G => let G' := eval unfold st2, pop_st, bc_st in G in change_no_check G' end). destruct (carve_fields SBEG (if fm then add_meter (op_famap (um_st bt st c) c) 0 [(sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg (um_st bt st c) c)), sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg (um_st bt st c) c)) + KFAMAP / 8)] 0 else um_st bt st c) c c) as (_ & _ & C3 & _).
            rewrite C3. destruct (um_st_reg bt st c) as [ER _]. destruct fm.
            - right. change (a_reg (add_meter (op_famap (um_st bt st c) c) 0 _ 0)) with (a_reg (op_famap (um_st bt st c) c)).
              destruct (famap_fields (um_st bt st c) c c) as (_ & _ & M3 & _). rewrite Z.eqb_refl in M3. rewrite M3, ER. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_fa] in G in change_no_check G' end). fold r mfa. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). lia.
            - left. rewrite ER. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_fa] in G in change_no_check G' end). fold r mfa. lia. }
          destruct (Z_lt_le_dec z (fa_beg SBEG c + mfa)) as [Lz | Lz]; [right; right; left; clear - Hin Lz; lia|].
          do 3 right. split; [clear - Hin Y7 Y8 MFA2 Lz; lia | left; clear - Hin Y7 MFA2 Lz; lia].
        * fold m. exact (GINVT M M2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GINV1 (fun a Ha => proj1 (FOOT2 a Ha))).
        * fold m RIz. (lazymatch goal with |- ?G => let G' := eval unfold gfp_regs in G in change_no_check G' end). fold spG spP. repeat split; assumption.
        * exact P10.
        * split; lia.
        * exact HretR.
        * intros r3 M3 mdl3 W3 RX3 SBM3 MI3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3. fold m in W3, RX3.
          assert (CNE : a_cache (op_refill st2 c m) c <> []) by (apply refill_cache_ne; rewrite LEN2; lia).
          apply (CONT1 fm r3 M3 mdl3 NFT W3 RX3 CNE).
          -- eapply same_except_vm_trans; [exact SEV2 | apply same_but_materialized_except_vm; exact SBM3].
          -- intros a Ha. rewrite (lazy_kept_sbm bt Lc FF mdl2 mdl3 SBM3 a Ha). exact (LK2 a Ha).
          -- exact (model_ivs_wf_sbm mdl2 mdl3 SBM3 MW2).
          -- exact (halted_sbm mdl2 mdl3 SBM3 HL2).
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end). fold RIz.
             destruct (decide (M3 a = M2 a)) as [E3' | NE3].
             ++ rewrite E3' in Ha |- *.
                ** destruct (FOOT2 a Ha) as [F Dd]. split; [| exact Dd]. unfold pop_foot in F. rewrite UspP in F. fold RIz in F.
                   destruct F as [F | [F | [F | F]]]; [left; clear - F; lia | right; left; exact F | right; right; right; left; exact F | right; right; right; right; clear - F; lia].
             ++ destruct (FOOT3 a NE3) as [F Dd]. split; [| exact Dd]. fold RIz in F. clear - F. lia.
          -- exact Q10. -- exact Q2. -- exact Q1. -- exact Q8. -- exact Q9. -- exact QS. -- rewrite Q4. exact P4. -- rewrite Q3. exact P3.
      + (* [comment removed for export] *)
        intros r2 M2 mdl2 st2 EST W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 (P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P4 & P3).
        replace (Z_to_bv 64 0x50d88 : word) with (0x50d88%bv : word) by (apply bv_eq; reflexivity).
        apply (refill_fail_K bt BT_segs BT_ia X (fun cf => katD ASEGS cf Qf) (liftable_katD Qf) c st2 Lc FF M2 rom mdl2 r2 spR raR s0R s1R
                 (Z_to_bv 64 (T + T_PC + PC_SZ * c)) (Z_to_bv 64 m)
                 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
                 Hc W2 RX2 HL2).
        * intros z Hz Hin. destruct (XOFF z Hz) as (_ & _ & _ & X4 & _). apply X4. lia.
        * exact (GINVT M M2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GINV1 (fun a Ha => proj1 (FOOT2 a Ha))).
        * exact P2.
        * fold RIz. exact P8.
        * exact P19.
        * exact P10.
        * split; lia.
        * exact HretR.
        * intros r3 M3 mdl3 RX3 SBM3 MI3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
          apply (CONT0 r3 M3 mdl3 st2 EST W2 RX3).
          -- eapply same_except_vm_trans; [exact SEV2 | apply same_but_materialized_except_vm; exact SBM3].
          -- intros a Ha. rewrite (lazy_kept_sbm bt Lc FF mdl2 mdl3 SBM3 a Ha). exact (LK2 a Ha).
          -- exact (model_ivs_wf_sbm mdl2 mdl3 SBM3 MW2).
          -- exact (halted_sbm mdl2 mdl3 SBM3 HL2).
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end). fold RIz.
             destruct (decide (M3 a = M2 a)) as [E3' | NE3].
             ++ rewrite E3' in Ha |- *.
                ** destruct (FOOT2 a Ha) as [F DZ]. unfold pop_foot in F. rewrite UspP in F. fold RIz in F. split; [| exact DZ].
                   destruct F as [F | [F | [F | F]]]; [left; clear - F; lia | right; left; exact F | right; right; right; left; exact F | right; right; right; right; clear - F; lia].
             ++ destruct (FOOT3 a NE3) as [F Dd]. fold RIz in F. split; [clear - F; lia | left; exact Dd].
          -- exact Q10. -- exact Q2. -- exact Q1. -- exact Q8. -- exact Q9. -- exact QS.
          -- rewrite Q4. exact P4.
          -- rewrite Q3. exact P3.
  Qed.

  Theorem refill_popN_tail :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp s0R s1R g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cinit st = true -> a_cache st c = [] -> a_kact st <= KCAP ->
    let r := a_reg st c in let au := r_alloc_user r in let mu := r_mapped_user r in let nf := Z.of_nat (length (r_free r)) in let mfa := r_mapped_fa r in
    let m := cache_hint c in
    nf < m -> au + csize c * (m - nf) <= mu ->
    (forall z, X z -> ~ pop_zone_t bt st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (T <= z < T + 2768)) ->
    U tp = TP ->
    (CEIL + 672 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    writableZ ASEGS M (U spR - 672) (U spR - 160) ->
    gf_inv bt M c spR raR s0R s1R (Z_to_bv 64 0x50a0c) (Z_to_bv 64 (T + T_PC + PC_SZ * c)) (Z_to_bv 64 m) g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 ->
    gfp_regs (at_ spR (-32)) (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16)) (reginfo bt c) SBEG c m regs ->
    getr regs 1 = Z_to_bv 64 0x50d88 -> getr regs 10 = Z_to_bv 64 0x103f18 -> getr regs 11 = at_ (Z_to_bv 64 T) 2768 -> getr regs 12 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 (reginfo bt c) -> getr regs 14 = Z_to_bv 64 (m - nf) -> getr regs 4 = tp -> getr regs 3 = gp ->
    (forall (fm : bool) (r' : bvmap 5 word) (M' : mem) mdl',
        (fm = false -> ~ ftest st c) ->
        let st' := op_refill (pop_st bt st c false fm) c m in
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' -> a_cache st' c <> [] ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill_foot bt st c (U spR) (U a) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = s0R -> getr r' 9 = s1R -> s_regs r' g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qok Qf) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ (st' = op_fhole st c /\ ftest st c)) ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill_foot bt st c (U spR) (U a) /\ (M' a <> None \/ pop_zone_t bt st c (U a))) ->
        getr r' 10 = Z_to_bv 64 0 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = s0R -> getr r' 9 = s1R -> s_regs r' g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 -> getr r' 4 = tp -> getr r' 3 = gp ->
        katD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x50dd4%bv : word) M rom) mdl) Qok Qf.
  Proof using N3FH N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs spR raR tp gp s0R s1R g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 Qok Qf Hc W RX HALT MW CINIT HC0 KC r au mu nf mfa m NF NOMAP XOFF
           Etp Hsp HretR WSTK GINV1 GR1 B1 B10 B11 B12 B13 B14 B4 B3 CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof (csize_pos c Hc) as [CS1 CS2]. pose proof (hint_size_le c Hc) as HSZ. fold m in HSZ.
    assert (Hm : 1 <= m <= 8) by ((lazymatch goal with |- ?G => let G' := eval unfold m, cache_hint in G in change_no_check G' end); lia).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _). fold mu au nf mfa in E2, E3, E4, E6, E7, E8.
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & _ & _ & T4k & _ & _).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (_ & _ & TSP & _ & S1 & S2 & S3).
    unfold KSPACE, PG, AS_HEAPLO in *.
    set (RIz := reginfo bt c) in *. assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    set (spG := at_ spR (-32)). assert (UspG : U spG = U spR - 32) by ((lazymatch goal with |- ?G => let G' := eval unfold spG in G in change_no_check G' end); rewrite at_u by lia; lia).
    set (spP := at_ spG (-128)). assert (UspP : U spP = U spR - 160) by ((lazymatch goal with |- ?G => let G' := eval unfold spP in G in change_no_check G' end); rewrite at_u by (rewrite UspG; lia); rewrite UspG; lia).
    assert (PZB : forall z, pop_zone_t bt st c z -> 0 < z < SBEG + 2 ^ 37) by (intros z Hz; exact (pop_zone_t_lt bt st Lc FF c z W Hc Hz)).
    (* [comment removed for export] *)
    assert (GINVT : forall (M1 M2 : mem) y0R y1R y_ra y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11,
               gf_inv bt M1 c spR raR y0R y1R y_ra y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 ->
               (forall a : word, M2 a <> M1 a -> pop_foot bt st c (U spP) (U a)) ->
               gf_inv bt M2 c spR raR y0R y1R y_ra y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11).
    { intros M1 M2 y0R y1R y_ra y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 (LK1 & GS1 & RS1) FT.
      assert (SAME : forall x : word, (RIz <= U x < RIz + 8) \/ (U spR - 160 <= U x < U spR) -> M2 x = M1 x).
      { intros x Hx. destruct (decide (M2 x = M1 x)) as [E | NE]; [exact E|]. exfalso. destruct (FT x NE) as [F | [F | [F | F]]].
        - rewrite UspP in F. lia.
        - pose proof (PZB _ F). lia.
        - clear - F Hx TSP ERI Hc T2 CR SP1. lia.
        - fold RIz in F. lia. }
      split; [| split].
      - rewrite <- LK1. apply rdn_ext; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply SAME. fold RIz. left. lia.
      - intros k v Hin. rewrite <- (GS1 k v Hin). fold spG.
        assert (Kk : -104 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        apply rdn_ext; [rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by (rewrite UspG; lia). rewrite UspG in Hx. cbn in Hx. apply SAME. right. lia.
      - intros k v Hin. rewrite <- (RS1 k v Hin).
        assert (Kk : -24 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        apply rdn_ext; [rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply SAME. right. lia. }
    fold r nf m RIz in GINV1, GR1, B13, B14.
      destruct GR1 as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22). fold spG spP in G2.
      assert (WST1 : writableZ ASEGS M (U spP - 512) (U spP)).
      { intros i Hi. rewrite UspP in Hi. apply WSTK. lia. }
      apply (populateN_katwD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3FH c st Lc FF M rom mdl regs spP (Z_to_bv 64 0x50d88)
               (Z_to_bv 64 RIz) (Z_to_bv 64 0x103f18) (Z_to_bv 64 (RIz + 8)) (Z_to_bv 64 (2 ^ 61)) (Z_to_bv 64 (SBEG + c * 2 ^ 32 + 0xE0000000))
               (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16)) (Z_to_bv 64 m) (at_ (Z_to_bv 64 T) 2768) tp gp (m - nf) Qok Qf
               Hc W RX HALT MW CINIT KC HC0 NF).
      + intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & X3 & X4 & _). exact (conj X1 (conj X2 (conj X3 X4))).
      + exact B1. + exact G2. + exact B4. + exact B3. + exact Etp. + exact B10. + exact B11. + exact B12. + exact B13. + exact B14.
      + exact G8. + exact G9. + exact G18. + exact G19. + exact G20. + exact G21. + exact G22.
      + rewrite UspP. split; lia.
      + apply ret_ok_lit; [lia | reflexivity].
      + split; [lia|]. clear - HSZ Hm NF E7 CS1. nia.
      + exact NOMAP.
      + exact WST1.
      + (* [comment removed for export] *)
        intros fm r2 M2 mdl2 NFT W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 (P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P4 & P3).
        set (st2 := pop_st bt st c false fm) in *.
        destruct (pop_st_facts bt st c false fm) as (F_ci & F_ca & F_fr). fold st2 r au mu in F_ci, F_ca, F_fr. rewrite Z.add_0_r in F_fr.
        set (newn := (mu - au) / csize c) in *.
        assert (N0 : m - nf <= newn).
        { (lazymatch goal with |- ?G => let G' := eval unfold newn in G in change_no_check G' end). apply Z.div_le_lower_bound; [lia|]. clear - NOMAP. lia. }
        assert (LEN2 : Z.of_nat (length (r_free (a_reg st2 c))) = nf + newn).
        { rewrite F_fr, length_app, Nat2Z.inj_add. fold nf. rewrite (carve_list_length bt c _ newn ltac:(lia)). reflexivity. }
        replace (Z_to_bv 64 0x50d88 : word) with (0x50d88%bv : word) by (apply bv_eq; reflexivity).
        apply (refill_ok_K bt BT_segs BT_ia X (fun cf => katwD ASEGS cf Qok Qf) (liftable_katwD Qok Qf) c st2 Lc FF M2 rom mdl2 r2 spR raR s0R s1R
                 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
                 Hc W2 RX2 HL2 ltac:(rewrite F_ci; exact CINIT) ltac:(rewrite F_ca; exact HC0)).
        * fold m. rewrite LEN2. lia.
        * intros z Hz. destruct (XOFF z Hz) as (X1 & _ & _ & X4 & X5). split; [exact X4|]. split; [| exact X5].
          rewrite LEN2. intros Hin. apply X1. (lazymatch goal with |- ?G => let G' := eval unfold pop_zone_t in G in change_no_check G' end). fold r mu mfa. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end).
          (* [comment removed for export] *)
          pose proof W2 as ((WR2 & _) & _). destruct (WR2 c Hc) as (_ & _ & _ & _ & _ & _ & Y7 & Y8 & _). rewrite LEN2 in Y7.
          assert (MFA2 : r_mapped_fa (a_reg st2 c) = mfa \/ r_mapped_fa (a_reg st2 c) = mfa + 2 ^ 18).
          { (lazymatch goal with |- ?G => let G' := eval unfold st2, pop_st, bc_st in G in change_no_check G' end). destruct (carve_fields SBEG (if fm then add_meter (op_famap st c) 0 [(sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg st c)), sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg st c)) + KFAMAP / 8)] 0 else st) c c) as (_ & _ & C3 & _).
            rewrite C3. destruct fm.
            - right. change (a_reg (add_meter (op_famap st c) 0 _ 0)) with (a_reg (op_famap st c)).
              destruct (famap_fields st c c) as (_ & _ & M3 & _). rewrite Z.eqb_refl in M3. rewrite M3. fold r mfa. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). lia.
            - left. fold r mfa. lia. }
          destruct (Z_lt_le_dec z (fa_beg SBEG c + mfa)) as [Lz | Lz]; [right; right; left; clear - Hin Lz; lia|].
          do 3 right. split; [clear - Hin Y7 Y8 MFA2 Lz; lia | left; clear - Hin Y7 MFA2 Lz; lia].
        * fold m. exact (GINVT M M2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GINV1 (fun a Ha => proj1 (FOOT2 a Ha))).
        * fold m RIz. (lazymatch goal with |- ?G => let G' := eval unfold gfp_regs in G in change_no_check G' end). fold spG spP. repeat split; assumption.
        * exact P10.
        * split; lia.
        * exact HretR.
        * intros r3 M3 mdl3 W3 RX3 SBM3 MI3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3. fold m in W3, RX3.
          assert (CNE : a_cache (op_refill st2 c m) c <> []) by (apply refill_cache_ne; rewrite LEN2; lia).
          apply (CONT1 fm r3 M3 mdl3 NFT W3 RX3 CNE).
          -- eapply same_except_vm_trans; [exact SEV2 | apply same_but_materialized_except_vm; exact SBM3].
          -- intros a Ha. rewrite (lazy_kept_sbm bt Lc FF mdl2 mdl3 SBM3 a Ha). exact (LK2 a Ha).
          -- exact (model_ivs_wf_sbm mdl2 mdl3 SBM3 MW2).
          -- exact (halted_sbm mdl2 mdl3 SBM3 HL2).
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end). fold RIz.
             destruct (decide (M3 a = M2 a)) as [E3' | NE3].
             ++ rewrite E3' in Ha |- *.
                ** destruct (FOOT2 a Ha) as [F Dd]. split; [| exact Dd]. unfold pop_foot in F. rewrite UspP in F. fold RIz in F.
                   destruct F as [F | [F | [F | F]]]; [left; clear - F; lia | right; left; exact F | right; right; right; left; exact F | right; right; right; right; clear - F; lia].
             ++ destruct (FOOT3 a NE3) as [F Dd]. split; [| exact Dd]. fold RIz in F. clear - F. lia.
          -- exact Q10. -- exact Q2. -- exact Q1. -- exact Q8. -- exact Q9. -- exact QS. -- rewrite Q4. exact P4. -- rewrite Q3. exact P3.
      + (* [comment removed for export] *)
        intros r2 M2 mdl2 st2 EST W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 (P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P4 & P3).
        replace (Z_to_bv 64 0x50d88 : word) with (0x50d88%bv : word) by (apply bv_eq; reflexivity).
        apply (refill_fail_K bt BT_segs BT_ia X (fun cf => katD ASEGS cf Qf) (liftable_katD Qf) c st2 Lc FF M2 rom mdl2 r2 spR raR s0R s1R
                 (Z_to_bv 64 (T + T_PC + PC_SZ * c)) (Z_to_bv 64 m)
                 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
                 Hc W2 RX2 HL2).
        * intros z Hz Hin. destruct (XOFF z Hz) as (_ & _ & _ & X4 & _). apply X4. lia.
        * exact (GINVT M M2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GINV1 (fun a Ha => proj1 (FOOT2 a Ha))).
        * exact P2.
        * fold RIz. exact P8.
        * exact P19.
        * exact P10.
        * split; lia.
        * exact HretR.
        * intros r3 M3 mdl3 RX3 SBM3 MI3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
          apply (CONT0 r3 M3 mdl3 st2 EST W2 RX3).
          -- eapply same_except_vm_trans; [exact SEV2 | apply same_but_materialized_except_vm; exact SBM3].
          -- intros a Ha. rewrite (lazy_kept_sbm bt Lc FF mdl2 mdl3 SBM3 a Ha). exact (LK2 a Ha).
          -- exact (model_ivs_wf_sbm mdl2 mdl3 SBM3 MW2).
          -- exact (halted_sbm mdl2 mdl3 SBM3 HL2).
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end). fold RIz.
             destruct (decide (M3 a = M2 a)) as [E3' | NE3].
             ++ rewrite E3' in Ha |- *.
                ** destruct (FOOT2 a Ha) as [F DZ]. unfold pop_foot in F. rewrite UspP in F. fold RIz in F. split; [| exact DZ].
                   destruct F as [F | [F | [F | F]]]; [left; clear - F; lia | right; left; exact F | right; right; right; left; exact F | right; right; right; right; clear - F; lia].
             ++ destruct (FOOT3 a NE3) as [F Dd]. fold RIz in F. split; [clear - F; lia | left; exact Dd].
          -- exact Q10. -- exact Q2. -- exact Q1. -- exact Q8. -- exact Q9. -- exact QS.
          -- rewrite Q4. exact P4.
          -- rewrite Q3. exact P3.
  Qed.


  Definition refill0_foot (st : ast) (c : Z) (sp : Z) (z : Z) : Prop :=
    refill_foot bt st c sp z \/ (T + T_PC + 84 <= z < T + T_PC + 2496).

  Theorem refill0_popM_katsD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cinit st = false -> a_cache st c = [] -> a_kact st <= KCAP -> mu_room st ->
    let st0 := op_cache_init st in
    let r := a_reg st c in let au := r_alloc_user r in let mu := r_mapped_user r in let nf := Z.of_nat (length (r_free r)) in let mfa := r_mapped_fa r in
    let m := cache_hint c in
    nf < m -> mu < au + csize c * (m - nf) ->
    (forall z, X z -> ~ pop_zone_t bt st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 (T + T_PC) ->
    getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) -> getr regs 12 = Z_to_bv 64 0x103f18 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 672 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    writableZ ASEGS M (U spR - 672) (U spR) ->
    (forall (fm : bool) (r' : bvmap 5 word) (M' : mem) mdl',
        (fm = false -> ~ ftest (um_st bt st0 c) c) ->
        let st' := op_refill (pop_st bt st0 c true fm) c m in
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' -> a_cache st' c <> [] ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot st c (U spR) (U a) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qok Qf) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st0 \/ st' = op_uhole st0 c \/ st' = um_st bt st0 c \/ (st' = op_fhole (um_st bt st0 c) c /\ ftest (um_st bt st0 c) c)) ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot st c (U spR) (U a) /\ (M' a <> None \/ pop_zone_t bt st c (U a))) ->
        getr r' 10 = Z_to_bv 64 0 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qf) ->
    katsD ASEGS (mkCfg (mkst regs (0x509cc%bv : word) M rom) mdl) Qok Qf.
  Proof using N3UH N3FH N3U N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs spR raR tp gp Qok Qf Hc W RX HALT MW CINIT HC0 KC MUR st0 r au mu nf mfa m NF NEEDMAP XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    apply (refill_head0_K bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X (fun cf => katsD ASEGS cf Qok Qf) (liftable_katsD Qok Qf)
             c st Lc FF M rom mdl regs spR raR tp gp Hc W RX HALT CINIT HC0 NF).
    - intros z Hz. destruct (XOFF z Hz) as (_ & X2 & _ & X4 & X5). exact (conj X4 (conj X2 X5)).
    - exact H1. - exact H2. - exact H4. - exact H3. - exact H10. - exact H11. - exact H12. - exact H13.
    - split; lia.
    - intros i Hi. apply WSTK. lia.
    - intros r1 M1 mdl1 W1 RX1 SBM1 MI1 FOOT1 GINV1 GR1 B1 B10 B11 B12 B13 B14 B4 B3.
      apply (refill_popM_tail c st0 Lc FF M1 rom mdl1 r1 spR raR tp gp (getr regs 8) (getr regs 9)
               (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) Qok Qf
               Hc W1 RX1 (halted_sbm mdl mdl1 SBM1 HALT) (model_ivs_wf_sbm mdl mdl1 SBM1 MW) eq_refl HC0 KC MUR NF NEEDMAP XOFF Etp (conj SP1 SP2) HretR).
      + intros i Hi. apply (repx_wr (fun _ => True) M1 M (fun a Ha => conj I (proj2 (FOOT1 a Ha))) (U spR - 672) (U spR) ltac:(lia) ltac:(lia) WSTK). lia.
      + exact GINV1. + exact GR1. + exact B1. + exact B10. + exact B11. + exact B12. + exact B13. + exact B14. + exact B4. + exact B3.
      + intros fm r3 M3 mdl3 NFT. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). intros W3 RX3 CNE3 SEV3 LK3 MW3 HL3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
        apply (CONT1 fm r3 M3 mdl3 NFT W3 RX3 CNE3).
        * eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV3].
        * intros a Ha. rewrite (LK3 a Ha). exact (lazy_kept_sbm bt Lc FF mdl mdl1 SBM1 a Ha).
        * exact MW3.
        * exact HL3.
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill0_foot in G in change_no_check G' end). destruct (decide (M3 a = M1 a)) as [E3' | NE3].
          -- rewrite E3' in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. split; [| exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end).
             destruct F as [F | [F | F]]; [left; left; clear - F; lia | left; right; right; right; right; clear - F; lia | right; exact F].
          -- destruct (FOOT3 a NE3) as [F Dd]. split; [left; exact F | exact Dd].
        * exact Q10. * exact Q2. * exact Q1. * exact Q8. * exact Q9. * exact QS. * exact Q4. * exact Q3.
      + intros r3 M3 mdl3 st3 EST W3 RX3 SEV3 LK3 MW3 HL3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
        apply (CONT0 r3 M3 mdl3 st3 EST W3 RX3).
        * eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV3].
        * intros a Ha. rewrite (LK3 a Ha). exact (lazy_kept_sbm bt Lc FF mdl mdl1 SBM1 a Ha).
        * exact MW3.
        * exact HL3.
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill0_foot in G in change_no_check G' end). destruct (decide (M3 a = M1 a)) as [E3' | NE3].
          -- rewrite E3' in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end). split; [| left; exact Dd].
             destruct F as [F | [F | F]]; [left; left; clear - F; lia | left; right; right; right; right; clear - F; lia | right; exact F].
          -- destruct (FOOT3 a NE3) as [F DZ]. split; [left; exact F | exact DZ].
        * exact Q10. * exact Q2. * exact Q1. * exact Q8. * exact Q9. * exact QS. * exact Q4. * exact Q3.
  Qed.

  Theorem refill0_popN_katwD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cinit st = false -> a_cache st c = [] -> a_kact st <= KCAP ->
    let st0 := op_cache_init st in
    let r := a_reg st c in let au := r_alloc_user r in let mu := r_mapped_user r in let nf := Z.of_nat (length (r_free r)) in let mfa := r_mapped_fa r in
    let m := cache_hint c in
    nf < m -> au + csize c * (m - nf) <= mu ->
    (forall z, X z -> ~ pop_zone_t bt st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 (T + T_PC) ->
    getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) -> getr regs 12 = Z_to_bv 64 0x103f18 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 672 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    writableZ ASEGS M (U spR - 672) (U spR) ->
    (forall (fm : bool) (r' : bvmap 5 word) (M' : mem) mdl',
        (fm = false -> ~ ftest st0 c) ->
        let st' := op_refill (pop_st bt st0 c false fm) c m in
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' -> a_cache st' c <> [] ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot st c (U spR) (U a) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qok Qf) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st0 \/ (st' = op_fhole st0 c /\ ftest st0 c)) ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot st c (U spR) (U a) /\ (M' a <> None \/ pop_zone_t bt st c (U a))) ->
        getr r' 10 = Z_to_bv 64 0 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x509cc%bv : word) M rom) mdl) Qok Qf.
  Proof using N3FH N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs spR raR tp gp Qok Qf Hc W RX HALT MW CINIT HC0 KC st0 r au mu nf mfa m NF NOMAP XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    apply (refill_head0_K bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X (fun cf => katwD ASEGS cf Qok Qf) (liftable_katwD Qok Qf)
             c st Lc FF M rom mdl regs spR raR tp gp Hc W RX HALT CINIT HC0 NF).
    - intros z Hz. destruct (XOFF z Hz) as (_ & X2 & _ & X4 & X5). exact (conj X4 (conj X2 X5)).
    - exact H1. - exact H2. - exact H4. - exact H3. - exact H10. - exact H11. - exact H12. - exact H13.
    - split; lia.
    - intros i Hi. apply WSTK. lia.
    - intros r1 M1 mdl1 W1 RX1 SBM1 MI1 FOOT1 GINV1 GR1 B1 B10 B11 B12 B13 B14 B4 B3.
      apply (refill_popN_tail c st0 Lc FF M1 rom mdl1 r1 spR raR tp gp (getr regs 8) (getr regs 9)
               (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) Qok Qf
               Hc W1 RX1 (halted_sbm mdl mdl1 SBM1 HALT) (model_ivs_wf_sbm mdl mdl1 SBM1 MW) eq_refl HC0 KC NF NOMAP XOFF Etp (conj SP1 SP2) HretR).
      + intros i Hi. apply (repx_wr (fun _ => True) M1 M (fun a Ha => conj I (proj2 (FOOT1 a Ha))) (U spR - 672) (U spR) ltac:(lia) ltac:(lia) WSTK). lia.
      + exact GINV1. + exact GR1. + exact B1. + exact B10. + exact B11. + exact B12. + exact B13. + exact B14. + exact B4. + exact B3.
      + intros fm r3 M3 mdl3 NFT. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). intros W3 RX3 CNE3 SEV3 LK3 MW3 HL3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
        apply (CONT1 fm r3 M3 mdl3 NFT W3 RX3 CNE3).
        * eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV3].
        * intros a Ha. rewrite (LK3 a Ha). exact (lazy_kept_sbm bt Lc FF mdl mdl1 SBM1 a Ha).
        * exact MW3.
        * exact HL3.
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill0_foot in G in change_no_check G' end). destruct (decide (M3 a = M1 a)) as [E3' | NE3].
          -- rewrite E3' in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. split; [| exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end).
             destruct F as [F | [F | F]]; [left; left; clear - F; lia | left; right; right; right; right; clear - F; lia | right; exact F].
          -- destruct (FOOT3 a NE3) as [F Dd]. split; [left; exact F | exact Dd].
        * exact Q10. * exact Q2. * exact Q1. * exact Q8. * exact Q9. * exact QS. * exact Q4. * exact Q3.
      + intros r3 M3 mdl3 st3 EST W3 RX3 SEV3 LK3 MW3 HL3 FOOT3 Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
        apply (CONT0 r3 M3 mdl3 st3 EST W3 RX3).
        * eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV3].
        * intros a Ha. rewrite (LK3 a Ha). exact (lazy_kept_sbm bt Lc FF mdl mdl1 SBM1 a Ha).
        * exact MW3.
        * exact HL3.
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold refill0_foot in G in change_no_check G' end). destruct (decide (M3 a = M1 a)) as [E3' | NE3].
          -- rewrite E3' in Ha |- *. destruct (FOOT1 a Ha) as [F Dd]. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end). split; [| left; exact Dd].
             destruct F as [F | [F | F]]; [left; left; clear - F; lia | left; right; right; right; right; clear - F; lia | right; exact F].
          -- destruct (FOOT3 a NE3) as [F DZ]. split; [left; exact F | exact DZ].
        * exact Q10. * exact Q2. * exact Q1. * exact Q8. * exact Q9. * exact QS. * exact Q4. * exact Q3.
  Qed.

End L3.
End WithCeil.
End AsAllocM8Lj.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8Lq.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8h OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Le AsAllocM8Lf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lh.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 AsAllocM8Li AsAllocM8Lj OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lp OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAllocMDm.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys7c.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).








Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  Hypothesis N3F : N3F_stmt bt.
  Hypothesis N3U : N3U_stmt bt.
  Hypothesis N3FH : AsKSys10.AsKSys7c.N3FH_stmt bt.     (* [comment removed for export] *)
  Hypothesis N3UH : AsKSys10.AsKSys7c.N3UH_stmt bt.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).

  Definition rf_st0 (st : ast) : ast := if a_cinit st then st else op_cache_init st.
  (* [comment removed for export] *)
  Definition utest_x (st : ast) (c : Z) : Prop :=
    r_mapped_user (a_reg st c) < r_alloc_user (a_reg st c) + csize c * (cache_hint c - Z.of_nat (length (r_free (a_reg st c)))).
  (* [comment removed for export] *)
  Definition refill_ok_st (st : ast) (c : Z) (st' : ast) : Prop :=
    (st' = op_refill st c (cache_hint c) /\ cache_hint c <= Z.of_nat (length (r_free (a_reg st c))))
    \/ exists um fm : bool, st' = op_refill (pop_st bt (rf_st0 st) c um fm) c (cache_hint c)
                            /\ (um = false -> ~ utest_x (rf_st0 st) c)
                            /\ (fm = false -> ~ ftest (if um then um_st bt (rf_st0 st) c else rf_st0 st) c).
  Definition utest (st : ast) (c : Z) : Prop := r_mapped_user (a_reg st c) < r_alloc_user (a_reg st c) + cache_hint c * csize c.
  Definition refill_fail_st (st : ast) (c : Z) (st' : ast) : Prop :=
    let s0 := rf_st0 st in
    (* [comment removed for export] *)
    Z.of_nat (length (r_free (a_reg s0 c))) < cache_hint c
    /\ (st' = s0 \/ (st' = op_uhole s0 c /\ utest s0 c) \/ (st' = um_st bt s0 c /\ utest s0 c)
        \/ (st' = op_fhole (um_st bt s0 c) c /\ utest s0 c /\ ftest (um_st bt s0 c) c) \/ (st' = op_fhole s0 c /\ ftest s0 c)).

  (* [comment removed for export] *)
  Lemma nofree_before_init : forall st Lc FF c, WF bt st Lc FF -> 1 <= c <= 30 -> a_cinit st = false -> r_free (a_reg st c) = [].
  Proof using.
    intros st Lc FF c W Hc CI. destruct (r_free (a_reg st c)) as [|k l] eqn:E; [reflexivity | exfalso].
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & Y9 & _).
    destruct (Y9 k ltac:(rewrite E; left; reflexivity)) as [_ CV].
    pose proof (cinit_of_carved bt st Lc FF _ _ c _ W Hc CV) as CT. rewrite CI in CT. discriminate CT.
  Qed.

  Theorem refill_katwD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cache st c = [] -> a_kact st <= KCAP -> mu_room st ->
    (forall z, X z -> ~ pop_zone_t bt st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 (T + T_PC) ->
    getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) -> getr regs 12 = Z_to_bv 64 0x103f18 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 672 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    writableZ ASEGS M (U spR - 672) (U spR) ->
    (forall (st' : ast) (r' : bvmap 5 word) (M' : mem) mdl',
        refill_ok_st st c st' ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' -> a_cache st' c <> [] ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot bt st c (U spR) (U a) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qok Qf) ->
    (forall (st' : ast) (r' : bvmap 5 word) (M' : mem) mdl',
        refill_fail_st st c st' ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot bt st c (U spR) (U a) /\ (M' a <> None \/ pop_zone_t bt st c (U a))) ->
        getr r' 10 = Z_to_bv 64 0 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x509cc%bv : word) M rom) mdl) Qok Qf.
  Proof using N3UH N3FH N3U N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs spR raR tp gp Qok Qf Hc W RX HALT MW HC0 KC MUR XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. pose proof Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
    destruct RF as (_ & _ & _ & _ & _ & E6 & E7 & _).
    set (r := a_reg st c) in *. set (au := r_alloc_user r). set (mu := r_mapped_user r). set (nf := Z.of_nat (length (r_free r))) in *.
    set (m := cache_hint c) in *.
    pose proof (csize_pos c Hc) as ((CSZ1 & CSZ2) & CSZ3).
    assert (NF0 : 0 <= nf) by ((lazymatch goal with |- ?G => let G' := eval unfold nf in G in change_no_check G' end); lia).
    assert (NUXOF : au + csize c * (m - nf) <= mu -> ~ utest_x st c) by (intros Hge; (lazymatch goal with |- ?G => let G' := eval unfold utest_x in G in change_no_check G' end); fold r; fold au mu nf m; lia).
    assert (UTOF : mu < au + csize c * (m - nf) -> utest st c).
    { intros NEED0. (lazymatch goal with |- ?G => let G' := eval unfold utest in G in change_no_check G' end). fold r. fold au mu m. clear - NEED0 NF0 CSZ1. nia. }
    destruct (a_cinit st) eqn:CI.
    - (* [comment removed for export] *)
      assert (S0 : rf_st0 st = st) by ((lazymatch goal with |- ?G => let G' := eval unfold rf_st0 in G in change_no_check G' end); rewrite CI; reflexivity).
      destruct (Z_lt_le_dec nf m) as [NF | LE].
      + destruct (Z_lt_le_dec mu (au + csize c * (m - nf))) as [NEED | NOMAP].
        * (* [comment removed for export] *)
          apply katsD_katwD.
          apply (refill_popM_katsD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3U N3FH N3UH c st Lc FF M rom mdl regs spR raR tp gp Qok Qf
                   Hc W RX HALT MW CI HC0 KC MUR NF NEED XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK).
          -- intros fm r' M' mdl' NFT. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). intros W' RX' CNE SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
             apply (CONT1 _ r' M' mdl' ltac:(right; exists true, fm; rewrite S0; split; [reflexivity | split; [intros X0; discriminate X0 | exact NFT]]) W' RX' CNE SEV LK MW' HL'); try assumption.
             intros a Ha. destruct (FOOT a Ha) as [F Dd]. split; [left; exact F | exact Dd].
          -- intros r' M' mdl' st' EST W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
             apply (CONT0 st' r' M' mdl'); try assumption.
             ++ (lazymatch goal with |- ?G => let G' := eval unfold refill_fail_st in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite S0. split; [exact NF|]. destruct EST as [E | [E | [E | [E FT]]]]; [left; exact E | right; left; split; [exact E | exact (UTOF NEED)] | right; right; left; split; [exact E | exact (UTOF NEED)] | right; right; right; left; split; [exact E | split; [exact (UTOF NEED) | exact FT]]].
             ++ intros a Ha. destruct (FOOT a Ha) as [F DZ]. split; [left; exact F | exact DZ].
        * (* [comment removed for export] *)
          apply (refill_popN_katwD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3FH c st Lc FF M rom mdl regs spR raR tp gp Qok Qf
                   Hc W RX HALT MW CI HC0 KC NF NOMAP XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK).
          -- intros fm r' M' mdl' NFT. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). intros W' RX' CNE SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
             apply (CONT1 _ r' M' mdl' ltac:(right; exists false, fm; rewrite S0; split; [reflexivity | split; [intros _; exact (NUXOF NOMAP) | exact NFT]]) W' RX' CNE SEV LK MW' HL'); try assumption.
             intros a Ha. destruct (FOOT a Ha) as [F Dd]. split; [left; exact F | exact Dd].
          -- intros r' M' mdl' st' EST W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
             apply (CONT0 st' r' M' mdl'); try assumption.
             ++ (lazymatch goal with |- ?G => let G' := eval unfold refill_fail_st in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite S0. split; [exact NF|]. destruct EST as [E | [E FT]]; [left; exact E | right; right; right; right; split; [exact E | exact FT]].
             ++ intros a Ha. destruct (FOOT a Ha) as [F DZ]. split; [left; exact F | exact DZ].
      + (* [comment removed for export] *)
        apply (refill_plain_K bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X (fun cf => katwD ASEGS cf Qok Qf) (liftable_katwD Qok Qf)
                 c st Lc FF M rom mdl regs spR raR Hc W RX HALT CI HC0 LE).
        * intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & _ & X4 & X5). split; [exact X4|]. split; [exact X2|]. split; [| exact X5].
          intros Hin. apply X1. (lazymatch goal with |- ?G => let G' := eval unfold pop_zone_t in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). right. right. left. fold r. fold r in Hin. fold nf in Hin. clear - Hin E7. lia.
        * exact H1. * exact H2. * exact H10. * exact H11. * exact H12. * exact H13.
        * split; lia.
        * exact HretR.
        * intros i Hi. apply WSTK. lia.
        * intros r' M' mdl' W' RX' CNE SBM MI' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
          apply (CONT1 _ r' M' mdl' ltac:(left; split; [reflexivity | exact LE]) W' RX' CNE (same_but_materialized_except_vm _ _ SBM) (lazy_kept_sbm bt Lc FF mdl mdl' SBM)
                   (model_ivs_wf_sbm mdl mdl' SBM MW) (halted_sbm mdl mdl' SBM HALT)); try assumption.
          -- intros a Ha. destruct (FOOT a Ha) as [F Dd]. split; [| exact Dd]. left. (lazymatch goal with |- ?G => let G' := eval unfold refill_foot in G in change_no_check G' end).
             destruct F as [F | [F | F]]; [left; clear - F; lia | right; right; right; right; exact F | right; right; left; exact F].
          -- rewrite Q4. exact H4.
          -- rewrite Q3. exact H3.
    - (* [comment removed for export] *)
      assert (S0 : rf_st0 st = op_cache_init st) by ((lazymatch goal with |- ?G => let G' := eval unfold rf_st0 in G in change_no_check G' end); rewrite CI; reflexivity).
      assert (NF : nf < m).
      { (lazymatch goal with |- ?G => let G' := eval unfold nf, r in G in change_no_check G' end). rewrite (nofree_before_init st Lc FF c W Hc CI). (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold m, cache_hint in G in change_no_check G' end). lia. }
      destruct (Z_lt_le_dec mu (au + csize c * (m - nf))) as [NEED | NOMAP].
      + apply katsD_katwD.
        apply (refill0_popM_katsD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3U N3FH N3UH c st Lc FF M rom mdl regs spR raR tp gp Qok Qf
                 Hc W RX HALT MW CI HC0 KC MUR NF NEED XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK).
        * intros fm r' M' mdl' NFT. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). intros W' RX' CNE SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
          apply (CONT1 _ r' M' mdl' ltac:(right; exists true, fm; rewrite S0; split; [reflexivity | split; [intros X0; discriminate X0 | exact NFT]]) W' RX' CNE SEV LK MW' HL'); assumption.
        * intros r' M' mdl' st' EST W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
          apply (CONT0 st' r' M' mdl'); try assumption.
          (lazymatch goal with |- ?G => let G' := eval unfold refill_fail_st in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite S0. split; [exact NF|]. destruct EST as [E | [E | [E | [E FT]]]]; [left; exact E | right; left; split; [exact E | exact (UTOF NEED)] | right; right; left; split; [exact E | exact (UTOF NEED)] | right; right; right; left; split; [exact E | split; [exact (UTOF NEED) | exact FT]]].
      + apply (refill0_popN_katwD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3FH c st Lc FF M rom mdl regs spR raR tp gp Qok Qf
                 Hc W RX HALT MW CI HC0 KC NF NOMAP XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK).
        * intros fm r' M' mdl' NFT. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). intros W' RX' CNE SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
          apply (CONT1 _ r' M' mdl' ltac:(right; exists false, fm; rewrite S0; split; [reflexivity | split; [intros _; exact (NUXOF NOMAP) | exact NFT]]) W' RX' CNE SEV LK MW' HL'); assumption.
        * intros r' M' mdl' st' EST W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
          apply (CONT0 st' r' M' mdl'); try assumption.
          (lazymatch goal with |- ?G => let G' := eval unfold refill_fail_st in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite S0. split; [exact NF|]. destruct EST as [E | [E FT]]; [left; exact E | right; right; right; right; split; [exact E | exact FT]].
  Qed.

  (* [comment removed for export] *)
  Theorem refill_katsD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cache st c = [] -> a_kact st <= KCAP -> mu_room st ->
    Z.of_nat (length (r_free (a_reg st c))) < cache_hint c -> utest_x st c ->
    (forall z, X z -> ~ pop_zone_t bt st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 (T + T_PC) ->
    getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) -> getr regs 12 = Z_to_bv 64 0x103f18 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 672 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    writableZ ASEGS M (U spR - 672) (U spR) ->
    (forall (st' : ast) (r' : bvmap 5 word) (M' : mem) mdl',
        refill_ok_st st c st' ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' -> a_cache st' c <> [] ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot bt st c (U spR) (U a) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qok Qf) ->
    (forall (st' : ast) (r' : bvmap 5 word) (M' : mem) mdl',
        refill_fail_st st c st' ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot bt st c (U spR) (U a) /\ (M' a <> None \/ pop_zone_t bt st c (U a))) ->
        getr r' 10 = Z_to_bv 64 0 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Qf) ->
    katsD ASEGS (mkCfg (mkst regs (0x509cc%bv : word) M rom) mdl) Qok Qf.
  Proof using N3UH N3FH N3U N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs spR raR tp gp Qok Qf Hc W RX HALT MW HC0 KC MUR ENF EUX XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. pose proof Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
    destruct RF as (_ & _ & _ & _ & _ & E6 & E7 & _).
    set (r := a_reg st c) in *. set (au := r_alloc_user r). set (mu := r_mapped_user r). set (nf := Z.of_nat (length (r_free r))) in *.
    set (m := cache_hint c) in *.
    pose proof (csize_pos c Hc) as ((CSZ1 & CSZ2) & CSZ3).
    assert (NF0 : 0 <= nf) by ((lazymatch goal with |- ?G => let G' := eval unfold nf in G in change_no_check G' end); lia).
    assert (NUXOF : au + csize c * (m - nf) <= mu -> ~ utest_x st c) by (intros Hge; (lazymatch goal with |- ?G => let G' := eval unfold utest_x in G in change_no_check G' end); fold r; fold au mu nf m; lia).
    assert (UTOF : mu < au + csize c * (m - nf) -> utest st c).
    { intros NEED0. (lazymatch goal with |- ?G => let G' := eval unfold utest in G in change_no_check G' end). fold r. fold au mu m. clear - NEED0 NF0 CSZ1. nia. }
    destruct (a_cinit st) eqn:CI.
    - (* [comment removed for export] *)
      assert (S0 : rf_st0 st = st) by ((lazymatch goal with |- ?G => let G' := eval unfold rf_st0 in G in change_no_check G' end); rewrite CI; reflexivity).
      destruct (Z_lt_le_dec nf m) as [NF | LE].
      + destruct (Z_lt_le_dec mu (au + csize c * (m - nf))) as [NEED | NOMAP].
        * (* [comment removed for export] *)
          apply (refill_popM_katsD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3U N3FH N3UH c st Lc FF M rom mdl regs spR raR tp gp Qok Qf
                   Hc W RX HALT MW CI HC0 KC MUR NF NEED XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK).
          -- intros fm r' M' mdl' NFT. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). intros W' RX' CNE SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
             apply (CONT1 _ r' M' mdl' ltac:(right; exists true, fm; rewrite S0; split; [reflexivity | split; [intros X0; discriminate X0 | exact NFT]]) W' RX' CNE SEV LK MW' HL'); try assumption.
             intros a Ha. destruct (FOOT a Ha) as [F Dd]. split; [left; exact F | exact Dd].
          -- intros r' M' mdl' st' EST W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
             apply (CONT0 st' r' M' mdl'); try assumption.
             ++ (lazymatch goal with |- ?G => let G' := eval unfold refill_fail_st in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite S0. split; [exact NF|]. destruct EST as [E | [E | [E | [E FT]]]]; [left; exact E | right; left; split; [exact E | exact (UTOF NEED)] | right; right; left; split; [exact E | exact (UTOF NEED)] | right; right; right; left; split; [exact E | split; [exact (UTOF NEED) | exact FT]]].
             ++ intros a Ha. destruct (FOOT a Ha) as [F DZ]. split; [left; exact F | exact DZ].
        * exfalso. exact (NUXOF NOMAP EUX).
      + exfalso. unfold m, nf, r in *. lia.
    - (* [comment removed for export] *)
      assert (S0 : rf_st0 st = op_cache_init st) by ((lazymatch goal with |- ?G => let G' := eval unfold rf_st0 in G in change_no_check G' end); rewrite CI; reflexivity).
      assert (NF : nf < m).
      { (lazymatch goal with |- ?G => let G' := eval unfold nf, r in G in change_no_check G' end). rewrite (nofree_before_init st Lc FF c W Hc CI). (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold m, cache_hint in G in change_no_check G' end). lia. }
      destruct (Z_lt_le_dec mu (au + csize c * (m - nf))) as [NEED | NOMAP].
      + apply (refill0_popM_katsD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F N3U N3FH N3UH c st Lc FF M rom mdl regs spR raR tp gp Qok Qf
                 Hc W RX HALT MW CI HC0 KC MUR NF NEED XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK).
        * intros fm r' M' mdl' NFT. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). intros W' RX' CNE SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
          apply (CONT1 _ r' M' mdl' ltac:(right; exists true, fm; rewrite S0; split; [reflexivity | split; [intros X0; discriminate X0 | exact NFT]]) W' RX' CNE SEV LK MW' HL'); assumption.
        * intros r' M' mdl' st' EST W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
          apply (CONT0 st' r' M' mdl'); try assumption.
          (lazymatch goal with |- ?G => let G' := eval unfold refill_fail_st in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite S0. split; [exact NF|]. destruct EST as [E | [E | [E | [E FT]]]]; [left; exact E | right; left; split; [exact E | exact (UTOF NEED)] | right; right; left; split; [exact E | exact (UTOF NEED)] | right; right; right; left; split; [exact E | split; [exact (UTOF NEED) | exact FT]]].
      + exfalso. exact (NUXOF NOMAP EUX).
  Qed.

  (* [comment removed for export] *)
  Theorem refill_katD_dm :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word) (Q : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cache st c = [] -> a_kact st <= KCAP -> mu_room st ->
    (forall z, X z -> ~ pop_zone_t bt st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 (T + T_PC) ->
    getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) -> getr regs 12 = Z_to_bv 64 0x103f18 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 672 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    writableZ ASEGS M (U spR - 672) (U spR) ->
    (forall (st' : ast) (r' : bvmap 5 word) (M' : mem) mdl',
        refill_ok_st st c st' ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' -> a_cache st' c <> [] ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot bt st c (U spR) (U a) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katD ASEGS (mkCfg (mkst r' raR M' rom) mdl') Q) ->
    (forall (st' : ast) (r' : bvmap 5 word) (M' : mem) mdl',
        refill_fail_st st c st' ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot bt st c (U spR) (U a) /\ (M' a <> None \/ pop_zone_t bt st c (U a))) ->
        getr r' 10 = Z_to_bv 64 0 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        doomed ASEGS (mkCfg (mkst r' raR M' rom) mdl')) ->
    katD ASEGS (mkCfg (mkst regs (0x509cc%bv : word) M rom) mdl) Q.
  Proof using N3UH N3FH N3U N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs spR raR tp gp Q Hc W RX HALT MW HC0 KC MUR XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK CONT1 CONT0.
    apply (katwD_dm ASEGS _ Q (doomed ASEGS)); [| intros c' Hd; exact Hd].
    apply (refill_katwD c st Lc FF M rom mdl regs spR raR tp gp Q (doomed ASEGS) Hc W RX HALT MW HC0 KC MUR XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 Hsp HretR WSTK).
    - intros st' r' M' mdl' EST W' RX' CNE SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3. apply katwD_of_katD.
      exact (CONT1 st' r' M' mdl' EST W' RX' CNE SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3).
    - intros st' r' M' mdl' EST W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3. apply katD_refl.
      exact (CONT0 st' r' M' mdl' EST W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3).
  Qed.
End L3.
End WithCeil.
End AsAllocM8Lq.
Module AsAllocM8Lr.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8h OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Le AsAllocM8Lf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lh.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 AsAllocM8Li AsAllocM8Lj OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lp OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAllocMDm AsAllocM8Lq.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).









Section FR.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Definition st_frame (st st' : ast) : Prop :=
    a_tq st' = a_tq st /\ a_gq st' = a_gq st /\ a_sec st' = a_sec st /\ a_dep st' = a_dep st /\ a_ialloc st' = a_ialloc st
    /\ a_kact st' = a_kact st /\ (exists naa, a_aa st' = a_aa st ++ naa).

  Lemma st_frame_refl : forall st, st_frame st st.
  Proof using. intros st. repeat split; try reflexivity. exists []. rewrite app_nil_r. reflexivity. Qed.
  Lemma st_frame_trans : forall s1 s2 s3, st_frame s1 s2 -> st_frame s2 s3 -> st_frame s1 s3.
  Proof using.
    intros s1 s2 s3 (A1 & A2 & A3 & A4 & A5 & A6 & (n1 & A7)) (B1 & B2 & B3 & B4 & B5 & B6 & (n2 & B7)).
    repeat split; try congruence. exists (n1 ++ n2). rewrite B7, A7, app_assoc. reflexivity.
  Qed.
  Lemma st_frame_set : forall st st', a_tq st' = a_tq st -> a_gq st' = a_gq st -> a_sec st' = a_sec st -> a_dep st' = a_dep st ->
    a_ialloc st' = a_ialloc st -> a_kact st' = a_kact st -> a_aa st' = a_aa st -> st_frame st st'.
  Proof using. intros st st' A1 A2 A3 A4 A5 A6 A7. repeat split; try assumption. exists []. rewrite app_nil_r. exact A7. Qed.

  Lemma st_frame_cache_init : forall st, st_frame st (op_cache_init st).
  Proof using. intros st. apply st_frame_set; reflexivity. Qed.
  Lemma st_frame_uhole : forall st c, st_frame st (op_uhole st c).
  Proof using. intros st c. apply st_frame_set; reflexivity. Qed.
  Lemma st_frame_fhole : forall st c, st_frame st (op_fhole st c).
  Proof using. intros st c. apply st_frame_set; reflexivity. Qed.
  Lemma st_frame_refill : forall st c m, st_frame st (op_refill st c m).
  Proof using. intros st c m. apply st_frame_set; reflexivity. Qed.
  Lemma st_frame_carve : forall st c, st_frame st (op_carve SBEG st c).
  Proof using. intros st c. destruct (carve_rest SBEG st c) as (_ & _ & A3 & A4 & A5 & _ & A7 & _ & A9 & A10 & A11 & _). apply st_frame_set; assumption. Qed.
  Lemma st_frame_meter0 : forall st naa, st_frame st (add_meter st 0 naa 0).
  Proof using. intros st naa. repeat split; try reflexivity; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply Z.add_0_r | exists naa; reflexivity]. Qed.
  Lemma st_frame_um : forall st c, st_frame st (um_st bt st c).
  Proof using.
    intros st c. (lazymatch goal with |- ?G => let G' := eval unfold um_st in G in change_no_check G' end). eapply st_frame_trans; [| apply st_frame_meter0]. apply st_frame_set; reflexivity.
  Qed.
  Lemma st_frame_famap : forall st c naa, st_frame st (add_meter (op_famap st c) 0 naa 0).
  Proof using.
    intros st c naa. eapply st_frame_trans; [| apply st_frame_meter0].
    destruct (famap_rest st c) as (_ & _ & A3 & A4 & A5 & _ & A7 & _ & A9 & A10 & A11 & _). apply st_frame_set; assumption.
  Qed.
  Lemma st_frame_pop : forall st c um fm, st_frame st (pop_st bt st c um fm).
  Proof using.
    intros st c um fm. (lazymatch goal with |- ?G => let G' := eval unfold pop_st, bc_st in G in change_no_check G' end).
    eapply st_frame_trans; [| apply st_frame_carve].
    assert (F1 : st_frame st (if um then um_st bt st c else st)) by (destruct um; [apply st_frame_um | apply st_frame_refl]).
    destruct fm; [| exact F1]. eapply st_frame_trans; [exact F1 | apply st_frame_famap].
  Qed.

  Theorem refill_ok_st_frame : forall st c st', refill_ok_st bt st c st' -> st_frame st st'.
  Proof using.
    intros st c st' [[-> _] | (um & fm & -> & _)]; [apply st_frame_refill|].
    eapply st_frame_trans; [| apply st_frame_refill]. eapply st_frame_trans; [| apply st_frame_pop].
    (lazymatch goal with |- ?G => let G' := eval unfold rf_st0 in G in change_no_check G' end). destruct (a_cinit st); [apply st_frame_refl | apply st_frame_cache_init].
  Qed.
  Theorem refill_fail_st_frame : forall st c st', refill_fail_st bt st c st' -> st_frame st st'.
  Proof using.
    intros st c st' H. unfold refill_fail_st in H. cbv zeta in H.
    assert (F0 : st_frame st (rf_st0 st)) by ((lazymatch goal with |- ?G => let G' := eval unfold rf_st0 in G in change_no_check G' end); destruct (a_cinit st); [apply st_frame_refl | apply st_frame_cache_init]).
    destruct H as (_ & [-> | [[-> _] | [[-> _] | [[-> _] | [-> _]]]]]).
    - exact F0.
    - eapply st_frame_trans; [exact F0 | apply st_frame_uhole].
    - eapply st_frame_trans; [exact F0 | apply st_frame_um].
    - eapply st_frame_trans; [exact F0|]. eapply st_frame_trans; [apply st_frame_um | apply st_frame_fhole].
    - eapply st_frame_trans; [exact F0 | apply st_frame_fhole].
  Qed.

  (* [comment removed for export] *)
  Definition flags_le (st st' : ast) : Prop :=
    forall c', (r_uhole (a_reg st' c') = true -> r_uhole (a_reg st c') = true) /\ (r_fhole (a_reg st' c') = true -> r_fhole (a_reg st c') = true).
  Lemma flags_le_refl : forall st, flags_le st st.
  Proof using. intros st c'. split; intros H; exact H. Qed.
  Lemma flags_le_trans : forall s1 s2 s3, flags_le s1 s2 -> flags_le s2 s3 -> flags_le s1 s3.
  Proof using. intros s1 s2 s3 A B c'. destruct (A c') as [A1 A2]. destruct (B c') as [B1 B2]. split; intros H; [exact (A1 (B1 H)) | exact (A2 (B2 H))]. Qed.
  Lemma flags_le_holes : forall st st', flags_le st st' -> forall h, holes_le h st -> holes_le h st'.
  Proof using. intros st st' FL h HL c' [Hu | Hf]; apply (HL c'); [left; exact (proj1 (FL c') Hu) | right; exact (proj2 (FL c') Hf)]. Qed.

  Ltac fl_tac := intros c'; (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_reg set_cache set_cinit add_meter] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end);
    let E := fresh "E" in destruct (Z.eqb c' _) eqn:E;
    [apply Z.eqb_eq in E; subst; (lazymatch goal with |- ?G => let G' := eval cbn [r_uhole r_fhole] in G in change_no_check G' end); split; intros H; first [discriminate H | exact H] | split; intros H; exact H].
  Lemma flags_le_cache_init : forall st, flags_le st (op_cache_init st).
  Proof using. intros st c'. split; intros H; exact H. Qed.
  Lemma flags_le_refill : forall st c m, flags_le st (op_refill st c m).
  Proof using. intros st c m. (lazymatch goal with |- ?G => let G' := eval unfold op_refill in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold set_cache in G in change_no_check G' end). fl_tac. Qed.
  Lemma flags_le_um : forall st c, flags_le st (um_st bt st c).
  Proof using. intros st c. (lazymatch goal with |- ?G => let G' := eval unfold um_st, op_usermap in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold add_meter, set_reg in G in change_no_check G' end). fl_tac. Qed.
  Lemma flags_le_famap : forall st c naa, flags_le st (add_meter (op_famap st c) 0 naa 0).
  Proof using.
    intros st c naa c'. change (a_reg (add_meter (op_famap st c) 0 naa 0)) with (a_reg (op_famap st c)).
    destruct (famap_fields st c c') as (_ & _ & _ & _ & F5 & F6). rewrite F5, F6. split; intros H; [exact H|].
    destruct (Z.eqb c' c); [discriminate H | exact H].
  Qed.
  Lemma flags_le_carve : forall st c, flags_le st (op_carve SBEG st c).
  Proof using. intros st c c'. destruct (carve_fields SBEG st c c') as (_ & _ & _ & _ & F5 & F6). cbv zeta in F5, F6. rewrite F5, F6. split; intros H; exact H. Qed.
  Lemma flags_le_pop : forall st c um fm, flags_le st (pop_st bt st c um fm).
  Proof using.
    intros st c um fm. (lazymatch goal with |- ?G => let G' := eval unfold pop_st, bc_st in G in change_no_check G' end).
    eapply flags_le_trans; [| apply flags_le_carve].
    assert (F1 : flags_le st (if um then um_st bt st c else st)) by (destruct um; [apply flags_le_um | apply flags_le_refl]).
    destruct fm; [| exact F1]. eapply flags_le_trans; [exact F1 | apply flags_le_famap].
  Qed.
  (* [comment removed for export] *)
  Theorem refill_ok_st_flags : forall st c st', refill_ok_st bt st c st' -> flags_le st st'.
  Proof using.
    intros st c st' H. destruct H as [[-> _] | (um & fm & -> & _)]; [apply flags_le_refill|].
    eapply flags_le_trans; [| apply flags_le_refill]. eapply flags_le_trans; [| apply flags_le_pop].
    (lazymatch goal with |- ?G => let G' := eval unfold rf_st0 in G in change_no_check G' end). destruct (a_cinit st); [apply flags_le_refl | apply flags_le_cache_init].
  Qed.
  Theorem refill_ok_st_holes : forall st c st', refill_ok_st bt st c st' -> forall h, holes_le h st -> holes_le h st'.
  Proof using. intros st c st' H. apply flags_le_holes. exact (refill_ok_st_flags st c st' H). Qed.
End FR.
End AsAllocM8Lr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8Lt.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3.
Import AsAllocM8Lf AsAllocM8Li AsAllocM8Lj.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithCeil.
Context {RC : run_ceil}.

Section L3t.
  Variable bt : as_boot.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).

  Lemma pop_zone_t_priv : forall st Lc FF c z, WF bt st Lc FF -> 1 <= c <= 30 -> pop_zone_t bt st c z -> rt_priv IA Lc FF z.
  Proof using.
    intros st Lc FF c z W Hc PZ. unfold pop_zone_t in PZ. cbv zeta in PZ.
    destruct PZ as [P | [P | [P | [RM [P | P]]]]].
    - exact (rt_priv_uslot bt st Lc FF W c z Hc P).
    - exact (rt_priv_uslot_shadow bt st Lc FF W c z Hc P).
    - apply (rt_priv_fa bt st Lc FF W c z Hc).
      pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & MF29 & _). lia.
    - exact (rt_priv_fslot bt st Lc FF W c z Hc RM P).
    - exact (rt_priv_fslot_shadow bt st Lc FF W c z Hc RM P).
  Qed.

  Lemma thread_page_priv : forall st Lc FF z, WF bt st Lc FF -> T <= z < T + PG -> rt_priv IA Lc FF z.
  Proof using.
    intros st Lc FF z W Hz. pose proof (free_obls_pf bt) as (_ & _ & OBL_rt_private & _).
    apply (OBL_rt_private st Lc FF z W). left. exact Hz.
  Qed.

  Theorem refill0_foot_priv : forall st Lc FF c sp z, WF bt st Lc FF -> 1 <= c <= 30 ->
    refill0_foot bt st c sp z -> (sp - 672 <= z < sp) \/ rt_priv IA Lc FF z.
  Proof using.
    intros st Lc FF c sp z W Hc F. unfold refill0_foot, refill_foot in F.
    destruct F as [[F | [F | [F | [F | F]]]] | F].
    - left. exact F.
    - right. exact (pop_zone_t_priv st Lc FF c z W Hc F).
    - right. apply (thread_page_priv st Lc FF z W). unfold T_PC, PC_SZ, PG in *. lia.
    - right. apply (thread_page_priv st Lc FF z W). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). lia.
    - right. exact (rt_priv_reginfo bt st Lc FF W c z Hc F).
    - right. apply (thread_page_priv st Lc FF z W). unfold T_PC, PG in *. lia.
  Qed.

  (* [comment removed for export] *)
  Corollary refill0_foot_lt : forall st Lc FF c sp z, WF bt st Lc FF -> 1 <= c <= 30 ->
    refill0_foot bt st c sp z -> (sp - 672 <= z < sp) \/ z < CEIL.
  Proof using.
    intros st Lc FF c sp z W Hc F. destruct (refill0_foot_priv st Lc FF c sp z W Hc F) as [S | (L & _)]; [left; exact S | right; exact L].
  Qed.
End L3t.
End WithCeil.
End AsAllocM8Lt.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvXShape3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFRefillG.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvXShape3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFArms.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Le AsAllocM8Lf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg AsAllocM8Li AsAllocM8Lj AsAllocM8Lq AsAllocM8Lr AsAllocM8Lt.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.

Section GLUE.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  #[local] Abbreviation T := (bt_thread bt).

  (* [comment removed for export] *)
  Lemma refill_ok_keeps : forall st st', refill_ok_st bt st BATCHCLASS st' -> free_keeps st st'.
  Proof using.
    intros st st' H. split.
    - intros S NS P.
      assert (P0 : prist S (rf_st0 st)) by ((lazymatch goal with |- ?G => let G' := eval unfold rf_st0 in G in change_no_check G' end); destruct (a_cinit st); [exact P | apply prist_cache_init; exact P]).
      destruct H as [[-> _] | (um & fm & -> & _)]; [apply prist_refill; [exact NS | exact P]|].
      apply prist_refill; [exact NS|]. (lazymatch goal with |- ?G => let G' := eval unfold pop_st, bc_st in G in change_no_check G' end). apply prist_carve; [exact NS|].
      assert (P1 : prist S (if um then um_st bt (rf_st0 st) BATCHCLASS else rf_st0 st)).
      { destruct um; [(lazymatch goal with |- ?G => let G' := eval unfold um_st in G in change_no_check G' end); apply prist_add_meter; apply prist_usermap; [exact NS | exact P0] | exact P0]. }
      destruct fm; [apply prist_add_meter; apply prist_famap; [exact NS | exact P1] | exact P1].
    - intros s Hs. destruct (refill_ok_st_frame bt st BATCHCLASS st' H) as (_ & _ & ES & _). rewrite <- ES. exact Hs.
  Qed.

  Variable TPm : Z.
  Hypothesis HTPm : TPm = ia_tp asan_addrs.
  (* [comment removed for export] *)
  Hypothesis REFILL_T :
    forall (fx : FPState) (X : Z -> Prop) (c : Z) st Lc FF (M rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word) (Q : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cache st c = [] -> a_kact st <= KCAP -> mu_room st ->
    (forall z, X z -> ~ pop_zone_t bt st c z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (bt_tctx bt + 152 <= z < bt_tctx bt + 160)
                      /\ ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TPm -> getr regs 10 = Z_to_bv 64 (T + T_PC) ->
    getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) -> getr regs 12 = Z_to_bv 64 0x103f18 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 672 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    writableZ ASEGS M (U spR - 672) (U spR) ->
    (forall (st' : ast) (r' : bvmap 5 word) (M' : mem) mdl',
        refill_ok_st bt st c st' ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' -> a_cache st' c <> [] ->
        same_except_vm mdl mdl' -> lazy_kept (bt_ia bt) Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot bt st c (U spR) (U a) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katD ASEGS (mkCfg (@mkst fx r' raR M' rom) mdl') Q) ->
    (forall (st' : ast) (r' : bvmap 5 word) (M' : mem) mdl',
        refill_fail_st bt st c st' ->
        WF bt st' Lc FF -> RepX bt X st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept (bt_ia bt) Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> refill0_foot bt st c (U spR) (U a) /\ (M' a <> None \/ pop_zone_t bt st c (U a))) ->
        getr r' 10 = Z_to_bv 64 0 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = tp -> getr r' 3 = gp ->
        doomed ASEGS (mkCfg (@mkst fx r' raR M' rom) mdl')) ->
    katD ASEGS (mkCfg (@mkst fx regs (0x509cc%bv : word) M rom) mdl) Q.

  Theorem hyp_refill24k_pf : HYP_REFILL24K_stmt bt FXOK 672.
  Proof using REFILL_T HTPm TPm BT_ia.
    (lazymatch goal with |- ?G => let G' := eval unfold HYP_REFILL24K_stmt in G in change_no_check G' end).
    intros fx X st Lc FF M mdl R sp ret HFX HH MW W RX XSH EC KC MUR R1 R2 R10 R11 R12 R13 R4 S16 Slo Shi RET SOK FAILD.
    pose proof ceil_rng as CR.
    assert (Hc : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    assert (PCE : Z_to_bv 64 0x509cc = (0x509cc%bv : word)) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (XOFF : forall z, X z -> ~ pop_zone_t bt st BATCHCLASS z /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (bt_tctx bt + 152 <= z < bt_tctx bt + 160)
                             /\ ~ (reginfo bt BATCHCLASS <= z < reginfo bt BATCHCLASS + 128) /\ ~ (T <= z < T + 2768)).
    { intros z Hz. pose proof (xshape_off_t bt st Lc FF _ _ W BATCHCLASS z Hc (XSH z Hz)) as XO. cbv zeta in XO.
      destruct XO as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8). rewrite BT_ia in O5. cbn [ia_img_lo ia_img_hi asan_addrs] in O5.
      split; [| split; [exact O5 | split; [exact O6 | split; [exact O7 | exact O8]]]].
      (lazymatch goal with |- ?G => let G' := eval unfold pop_zone_t in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). intros [P | [P | [P | (RM & [P | P])]]]; [exact (O1 P) | exact (O2 P) | exact (O3 P) | exact (proj1 (O4 RM) P) | exact (proj2 (O4 RM) P)]. }
    rewrite PCE.
    apply (REFILL_T fx X BATCHCLASS st Lc FF M (seg_rom ASEGS) mdl R sp ret (getr R 4) (getr R 3)
             (refill24_post_k bt FXOK 672 X st Lc FF M mdl R sp ret) Hc W RX HH MW EC KC MUR XOFF R1 R2 eq_refl eq_refl).
    - rewrite R4, HTPm, BT_ia. reflexivity.
    - exact R10.
    - exact R11.
    - rewrite R12. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. reflexivity.
    - exact R13.
    - unfold PTRHI in Shi. clear - Slo Shi. lia.
    - exact RET.
    - intros i Hi. assert (Ui : U (Z_to_bv 64 i) = i) by (apply u_Z2bv; unfold PTRHI in Shi; clear - Hi Slo Shi CR; lia).
      apply (SOK (Z_to_bv 64 i)). rewrite Ui. exact Hi.
    - (* [comment removed for export] *)
      intros st' r' M' mdl' EST W' RX' CNE SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
      apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold refill24_post_k in G in change_no_check G' end).
      destruct (list_nil_or_snoc (a_cache st' BATCHCLASS)) as [E0 | (ks & k & EK)]; [exfalso; exact (CNE E0)|].
      destruct (refill_ok_st_frame bt st BATCHCLASS st' EST) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
      exists fx, st', M', mdl', r', ks, k.
      split; [reflexivity|]. split; [exact HFX|]. split; [exact HL'|]. split; [exact W'|]. split; [exact RX'|]. split; [exact EK|].
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [exact F6|]. split; [exact F7|].
      split.
      { (* [comment removed for export] *)
        intros a Ha OUT NST. destruct (decide (M' a = M a)) as [E | NE]; [exact E | exfalso].
        destruct (FOOT a NE) as [F _]. destruct (XOFF (U a) Ha) as (X1 & _ & _ & X4 & X5).
        unfold refill0_foot, refill_foot in F. unfold T_PC, PC_SZ, BATCHCLASS in *.
        destruct F as [[F | [F | [F | [F | F]]]] | F]; [clear - F OUT; lia | exact (X1 F) | apply X5; clear - F; lia | apply NST; clear - F; lia | exact (X4 F) | apply X5; clear - F; lia]. }
      split.
      { intros a NE. destruct (FOOT a NE) as [F D]. split; [| exact D].
        destruct (refill0_foot_priv bt st Lc FF BATCHCLASS (U sp) (U a) W Hc F) as [S | P]; [left; exact S | right; left; exact P]. }
      split; [exact LK|].
      split.
      { destruct QS as (S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27).
        apply regs_kept_intro; [rewrite Q2; symmetry; exact R2 | exact Q3 | exact Q4 | exact Q8 | exact Q9 | exact S18 | exact S19 | exact S20 | exact S21 | exact S22
                               | exact S23 | exact S24 | exact S25 | exact S26 | exact S27]. }
      split; [exact Q10|]. split; [exact SEV|]. split; [exact MW'|].
      split; [exact (refill_ok_st_holes bt st BATCHCLASS st' EST) | exact (refill_ok_keeps st st' EST)].
    - (* [comment removed for export] *)
      intros st' r' M' mdl' EST W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
      apply FAILD. (lazymatch goal with |- ?G => let G' := eval unfold refill24_fail_post_k in G in change_no_check G' end). exists fx, st', M', mdl', r'.
      split; [reflexivity|]. split; [exact HFX|]. split; [exact HL'|]. split; [exact W'|]. split; [exact RX' | exact Q10].
  Qed.
End GLUE.
End AsAllocFRefillG.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8Ls.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8h OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Le AsAllocM8Lf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lh.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 AsAllocM8Li AsAllocM8Lj OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lp OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAllocMDm AsAllocM8Lq.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys7c.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).









Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.
Section G.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis BOOTG : boot_geom bt.

  Lemma n3f_of_boot : AsAllocM8Lc.N3F_stmt bt.
  Proof using BOOTG. exact (AsKSys7b.N3F_pf bt (proj1 BOOTG)). Qed.
  Lemma n3u_of_boot : AsAllocM8Ld.N3U_stmt bt.
  Proof using BOOTG. exact (AsKSys7b.N3U_pf bt (proj1 BOOTG)). Qed.
  (* [comment removed for export] *)
  Lemma n3fh_of_boot : AsKSys10.AsKSys7c.N3FH_stmt bt.
  Proof using BOOTG. exact (AsKSys10.AsKSys7c.N3FH_pf bt (proj1 BOOTG)). Qed.
  Lemma n3uh_of_boot : AsKSys10.AsKSys7c.N3UH_stmt bt.
  Proof using BOOTG. exact (AsKSys10.AsKSys7c.N3UH_pf bt (proj1 BOOTG)). Qed.

  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.

  Definition refill_katwD_b := refill_katwD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X n3f_of_boot n3u_of_boot n3fh_of_boot n3uh_of_boot.
  Definition refill_katsD_b := refill_katsD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X n3f_of_boot n3u_of_boot n3fh_of_boot n3uh_of_boot.
  Definition refill_katD_dm_b := refill_katD_dm bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X n3f_of_boot n3u_of_boot n3fh_of_boot n3uh_of_boot.
End G.
End WithCeil.
End AsAllocM8Ls.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMHoleN.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Le AsAllocM8Lf AsAllocM8Lq AsAllocM8Lr OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithCeil.
Context {RC : run_ceil}.

Section HN.
  Variable bt : as_boot.


  (* [comment removed for export] *)
  Lemma fail_st_regs : forall st c st', refill_fail_st bt st c st' ->
    let r := a_reg st c in
    (forall c0, c0 <> c -> a_reg st' c0 = a_reg st c0)
    /\ a_cache st' c = a_cache st c
    /\ Z.of_nat (length (r_free r)) < cache_hint c
    /\ exists (mu' : Z) (uh fh : bool),
         a_reg st' c = REG mu' (r_alloc_user r) (r_mapped_fa r) (r_free r) uh fh
         /\ (uh = true -> mu' = r_mapped_user r /\ (r_uhole r = true \/ utest st c))
         /\ (fh = true -> (r_fhole r = true /\ (mu' = r_mapped_user r \/ (mu' = r_mapped_user r + KUSERMAP /\ utest st c)))
                          \/ r_mapped_fa r < 4 * (Z.of_nat (length (r_free r)) + (mu' - r_alloc_user r) / csize c)).
  Proof using.
    intros st c st' EST r. unfold refill_fail_st in EST. cbv zeta in EST. destruct EST as (NFc & EST).
    assert (S0R : a_reg (rf_st0 st) = a_reg st) by ((lazymatch goal with |- ?G => let G' := eval unfold rf_st0 in G in change_no_check G' end); destruct (a_cinit st); reflexivity).
    assert (S0C : a_cache (rf_st0 st) = a_cache st) by ((lazymatch goal with |- ?G => let G' := eval unfold rf_st0 in G in change_no_check G' end); destruct (a_cinit st); reflexivity).
    assert (UTE : utest (rf_st0 st) c = utest st c) by ((lazymatch goal with |- ?G => let G' := eval unfold utest in G in change_no_check G' end); rewrite S0R; reflexivity).
    rewrite S0R in NFc. fold r in NFc.
    destruct EST as [-> | [[-> UT] | [[-> UT] | [[-> [UT FT]] | [-> FT]]]]].
    - (* [comment removed for export] *)
      split; [intros c0 _; rewrite S0R; reflexivity|]. split; [rewrite S0C; reflexivity|]. split; [exact NFc|].
      exists (r_mapped_user r), (r_uhole r), (r_fhole r). rewrite S0R. fold r.
      split; [destruct r; reflexivity|]. split; [intros X; split; [reflexivity | left; exact X] | intros X; left; split; [exact X | left; reflexivity]].
    - (* [comment removed for export] *)
      rewrite UTE in UT.
      split; [intros c0 NE; (lazymatch goal with |- ?G => let G' := eval unfold op_uhole, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); rewrite S0R; apply fupdZ_other; exact NE|].
      split; [(lazymatch goal with |- ?G => let G' := eval unfold op_uhole, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_cache] in G in change_no_check G' end); rewrite S0C; reflexivity|]. split; [exact NFc|].
      exists (r_mapped_user r), true, (r_fhole r).
      split; [(lazymatch goal with |- ?G => let G' := eval unfold op_uhole, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); rewrite S0R, fupdZ_same; fold r; reflexivity|].
      split; [intros _; split; [reflexivity | right; exact UT] | intros X; left; split; [exact X | left; reflexivity]].
    - (* [comment removed for export] *)
      rewrite UTE in UT.
      split; [intros c0 NE; (lazymatch goal with |- ?G => let G' := eval unfold um_st, op_usermap, add_meter, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); rewrite S0R; apply fupdZ_other; exact NE|].
      split; [(lazymatch goal with |- ?G => let G' := eval unfold um_st, op_usermap, add_meter, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_cache] in G in change_no_check G' end); rewrite S0C; reflexivity|]. split; [exact NFc|].
      exists (r_mapped_user r + KUSERMAP), false, (r_fhole r).
      split; [(lazymatch goal with |- ?G => let G' := eval unfold um_st, op_usermap, add_meter, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); rewrite S0R, fupdZ_same; fold r; reflexivity|].
      split; [intros X; discriminate X | intros X; left; split; [exact X | right; split; [reflexivity | exact UT]]].
    - (* [comment removed for export] *)
      assert (ER : a_reg (um_st bt (rf_st0 st) c) c = REG (r_mapped_user r + KUSERMAP) (r_alloc_user r) (r_mapped_fa r) (r_free r) false (r_fhole r)).
      { (lazymatch goal with |- ?G => let G' := eval unfold um_st, op_usermap, add_meter, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). rewrite S0R, fupdZ_same. fold r. reflexivity. }
      unfold ftest in FT. rewrite ER in FT. cbn [r_mapped_fa r_free] in FT. unfold carve_n in FT. cbn [r_mapped_user r_alloc_user] in FT.
      split; [intros c0 NE; (lazymatch goal with |- ?G => let G' := eval unfold op_fhole, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); rewrite fupdZ_other by exact NE;
              (lazymatch goal with |- ?G => let G' := eval unfold um_st, op_usermap, add_meter, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); rewrite S0R; apply fupdZ_other; exact NE|].
      split; [(lazymatch goal with |- ?G => let G' := eval unfold op_fhole, um_st, op_usermap, add_meter, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_cache] in G in change_no_check G' end); rewrite S0C; reflexivity|]. split; [exact NFc|].
      exists (r_mapped_user r + KUSERMAP), false, true.
      split; [(lazymatch goal with |- ?G => let G' := eval unfold op_fhole, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); rewrite fupdZ_same, ER; reflexivity|].
      split; [intros X; discriminate X | intros _; right; exact FT].
    - (* [comment removed for export] *)
      unfold ftest in FT. rewrite S0R in FT. fold r in FT. unfold carve_n in FT.
      split; [intros c0 NE; (lazymatch goal with |- ?G => let G' := eval unfold op_fhole, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); rewrite S0R; apply fupdZ_other; exact NE|].
      split; [(lazymatch goal with |- ?G => let G' := eval unfold op_fhole, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_cache] in G in change_no_check G' end); rewrite S0C; reflexivity|]. split; [exact NFc|].
      exists (r_mapped_user r), (r_uhole r), true.
      split; [(lazymatch goal with |- ?G => let G' := eval unfold op_fhole, set_reg in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); rewrite S0R, fupdZ_same; fold r; reflexivity|].
      split; [intros X; split; [reflexivity | left; exact X] | intros _; right; exact FT].
  Qed.

  (* [comment removed for export] *)
  Theorem holes_ls_fail : forall n st st', 1 <= n <= 64512 -> holes_ls n st ->
    a_cache st (class_of (needed n)) = [] ->
    refill_fail_st bt st (class_of (needed n)) st' -> holes_ls n st'.
  Proof using.
    intros n st st' Hn HS HC0 EST. set (c := class_of (needed n)) in *.
    pose proof (mc_needed n Hn) as (_ & _ & Hc & _). fold c in Hc.
    pose proof (csize_pos c Hc) as ((CS1 & CS2) & CS3).
    destruct (fail_st_regs st c st' EST) as (OTH & EC & NFc & mu' & uh & fh & ER & UHC & FHC).
    intros c0 Hfl.
    destruct (Z.eq_dec c0 c) as [-> | NE].
    2:{ exfalso. rewrite (OTH c0 NE) in Hfl. destruct (HS c0 Hfl) as ((_ & Ec) & _). exact (NE Ec). }
    rewrite ER. rewrite ER in Hfl. cbn [r_uhole r_fhole r_free r_mapped_user r_alloc_user r_mapped_fa] in *.
    split; [split; [lia | reflexivity]|]. split; [rewrite EC; exact HC0|]. split; [exact NFc|].
    assert (MONO : forall m1 m2, m1 <= m2 -> (m1 - r_alloc_user (a_reg st c)) / csize c <= (m2 - r_alloc_user (a_reg st c)) / csize c).
    { intros m1 m2 Hm. apply Z.div_le_mono; lia. }
    assert (PMU : forall m0, m0 <= (if m0 <? r_alloc_user (a_reg st c) + cache_hint c * csize c then m0 + KUSERMAP else m0)).
    { intros m0. destruct (m0 <? r_alloc_user (a_reg st c) + cache_hint c * csize c); (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia. }
    split.
    - intros Uh. destruct (UHC Uh) as [Emu [U0 | UT]]; rewrite Emu.
      + destruct (HS c (or_introl U0)) as (_ & _ & _ & EU & _). exact (EU U0).
      + exact UT.
    - intros Fh. (lazymatch goal with |- ?G => let G' := eval unfold pop_newn, pop_mu in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end).
      destruct (FHC Fh) as [[F0 EM] | FT].
      + destruct (HS c (or_intror F0)) as (_ & _ & _ & _ & EF). pose proof (EF F0) as E1. unfold pop_newn, pop_mu in E1.
        destruct EM as [-> | [-> UT]]; [exact E1|].
        unfold utest in UT. rewrite (proj2 (Z.ltb_lt _ _) UT) in E1.
        pose proof (MONO _ _ (PMU (r_mapped_user (a_reg st c) + KUSERMAP))). lia.
      + pose proof (MONO _ _ (PMU mu')). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma refill_keeps_flags : forall s c m, r_uhole (a_reg (op_refill s c m) c) = r_uhole (a_reg s c) /\ r_fhole (a_reg (op_refill s c m) c) = r_fhole (a_reg s c).
  Proof using. intros s c m. (lazymatch goal with |- ?G => let G' := eval unfold op_refill, set_cache, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). rewrite fupdZ_same. (lazymatch goal with |- ?G => let G' := eval cbn [r_uhole r_fhole] in G in change_no_check G' end). split; reflexivity. Qed.

  Lemma pop_st_flags : forall s0 c um fm,
    r_uhole (a_reg (pop_st bt s0 c um fm) c) = (if um then false else r_uhole (a_reg s0 c))
    /\ r_fhole (a_reg (pop_st bt s0 c um fm) c) = (if fm then false else r_fhole (a_reg s0 c)).
  Proof using.
    intros s0 c um fm. (lazymatch goal with |- ?G => let G' := eval unfold pop_st, bc_st in G in change_no_check G' end).
    set (s1 := if um then um_st bt s0 c else s0).
    assert (F1 : r_uhole (a_reg s1 c) = (if um then false else r_uhole (a_reg s0 c)) /\ r_fhole (a_reg s1 c) = r_fhole (a_reg s0 c)).
    { (lazymatch goal with |- ?G => let G' := eval unfold s1 in G in change_no_check G' end). destruct um; [| split; reflexivity].
      (lazymatch goal with |- ?G => let G' := eval unfold um_st in G in change_no_check G' end). change (a_reg (add_meter (op_usermap s0 c) 0 _ 0)) with (a_reg (op_usermap s0 c)).
      destruct (usermap_fields s0 c c) as (_ & _ & _ & _ & U5 & U6). rewrite Z.eqb_refl in U5. split; [exact U5 | exact U6]. }
    destruct F1 as [F1u F1f].
    match goal with |- context [op_carve _ ?s2 c] => set (S2 := s2) end.
    assert (F2 : r_uhole (a_reg S2 c) = r_uhole (a_reg s1 c) /\ r_fhole (a_reg S2 c) = (if fm then false else r_fhole (a_reg s1 c))).
    { (lazymatch goal with |- ?G => let G' := eval unfold S2 in G in change_no_check G' end). destruct fm; [| split; reflexivity].
      match goal with |- context [a_reg (add_meter ?x 0 ?y 0)] => change (a_reg (add_meter x 0 y 0)) with (a_reg x) end.
      destruct (famap_fields s1 c c) as (_ & _ & _ & _ & U5 & U6). rewrite Z.eqb_refl in U6. split; [exact U5 | exact U6]. }
    destruct F2 as [F2u F2f].
    destruct (carve_fields (bt_spacebeg bt) S2 c c) as (_ & _ & _ & _ & C5 & C6). cbn zeta in C5, C6.
    rewrite C5, C6, F2u, F2f, F1u, F1f. split; [reflexivity | destruct fm; reflexivity].
  Qed.

  Theorem holes_closed_ok : forall n st Lc FF st', 1 <= n <= 64512 -> WF bt st Lc FF -> holes_ls n st ->
    a_cache st (class_of (needed n)) = [] ->
    refill_ok_st bt st (class_of (needed n)) st' ->
    forall c0, r_uhole (a_reg st' c0) = false /\ r_fhole (a_reg st' c0) = false.
  Proof using.
    intros n st Lc FF st' Hn W HS HC0 EST c0. set (c := class_of (needed n)) in *.
    pose proof (mc_needed n Hn) as (_ & _ & Hc & _). fold c in Hc.
    pose proof (csize_pos c Hc) as ((CS1 & CS2) & CS3). pose proof (hint_size_le c Hc) as HSL.
    pose proof (refill_ok_st_flags bt st c st' EST) as FL.
    destruct (Z.eq_dec c0 c) as [-> | NE].
    2:{ destruct (FL c0) as [F1 F2].
        destruct (r_uhole (a_reg st' c0)) eqn:U1; [exfalso; destruct (HS c0 (or_introl (F1 eq_refl))) as ((_ & Ec) & _); exact (NE Ec)|].
        destruct (r_fhole (a_reg st' c0)) eqn:U2; [exfalso; destruct (HS c0 (or_intror (F2 eq_refl))) as ((_ & Ec) & _); exact (NE Ec)|]. split; reflexivity. }
    (* [comment removed for export] *)
    assert (ENT : r_uhole (a_reg st c) = true \/ r_fhole (a_reg st c) = true ->
              Z.of_nat (length (r_free (a_reg st c))) < cache_hint c
              /\ (r_uhole (a_reg st c) = true -> r_mapped_user (a_reg st c) < r_alloc_user (a_reg st c) + cache_hint c * csize c)
              /\ (r_fhole (a_reg st c) = true -> r_mapped_fa (a_reg st c) < 4 * (Z.of_nat (length (r_free (a_reg st c))) + pop_newn (a_reg st c) c))).
    { intros Hf. destruct (HS c Hf) as (_ & _ & E3 & E4 & E5). exact (conj E3 (conj E4 E5)). }
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((_ & TI & _) & _).
    set (r := a_reg st c) in *. set (mu := r_mapped_user r) in *. set (au := r_alloc_user r) in *. set (nf := Z.of_nat (length (r_free r))) in *.
    set (mfa := r_mapped_fa r) in *. set (m := cache_hint c) in *.
    assert (S0R : a_reg (rf_st0 st) = a_reg st) by ((lazymatch goal with |- ?G => let G' := eval unfold rf_st0 in G in change_no_check G' end); destruct (a_cinit st); reflexivity).
    destruct EST as [[-> LE] | (um & fm & -> & NU & NF)].
    - (* [comment removed for export] *)
      destruct (refill_keeps_flags st c m) as [K1 K2]. fold m. rewrite K1, K2. fold r.
      destruct (r_uhole r) eqn:U1; [exfalso; destruct (ENT (or_introl eq_refl)) as (E3 & _); unfold m, nf, r in *; lia|].
      destruct (r_fhole r) eqn:U2; [exfalso; destruct (ENT (or_intror eq_refl)) as (E3 & _); unfold m, nf, r in *; lia|]. split; reflexivity.
    - destruct (refill_keeps_flags (pop_st bt (rf_st0 st) c um fm) c m) as [K1 K2]. fold m. rewrite K1, K2.
      destruct (pop_st_flags (rf_st0 st) c um fm) as [P1 P2]. rewrite P1, P2, S0R. fold r.
      (* [comment removed for export] *)
      assert (UX : r_uhole r = true \/ r_fhole r = true -> mu < au + m * csize c -> utest_x (rf_st0 st) c).
      { intros Hf WK. destruct (ENT Hf) as (E3 & _). (lazymatch goal with |- ?G => let G' := eval unfold utest_x in G in change_no_check G' end). rewrite S0R. fold r mu au nf m.
        destruct TI as [T1 | T2]; [| unfold KUSERMAP in T2; lia].
        assert (csize c <= csize c * (m - nf)) by nia. lia. }
      split.
      + destruct um; [reflexivity|]. destruct (r_uhole r) eqn:U1; [exfalso | reflexivity].
        destruct (ENT (or_introl eq_refl)) as (_ & E4 & _). exact (NU eq_refl (UX (or_introl eq_refl) (E4 eq_refl))).
      + destruct fm; [reflexivity|]. destruct (r_fhole r) eqn:U2; [exfalso | reflexivity].
        destruct (ENT (or_intror eq_refl)) as (E3 & _ & E5). pose proof (E5 eq_refl) as EF. unfold pop_newn, pop_mu in EF. fold mu au m in EF.
        apply (NF eq_refl). (lazymatch goal with |- ?G => let G' := eval unfold ftest in G in change_no_check G' end).
        assert (MONO : forall m1 m2, m1 <= m2 -> (m1 - au) / csize c <= (m2 - au) / csize c) by (intros m1 m2 Hm; apply Z.div_le_mono; lia).
        destruct um.
        * (* [comment removed for export] *)
          assert (ER : a_reg (um_st bt (rf_st0 st) c) c = REG (mu + KUSERMAP) au mfa (r_free r) false (r_fhole r)).
          { (lazymatch goal with |- ?G => let G' := eval unfold um_st, op_usermap, add_meter, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). rewrite S0R, fupdZ_same. reflexivity. }
          rewrite ER. (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_fa r_free] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user] in G in change_no_check G' end). fold nf.
          assert (PM : (if mu <? au + m * csize c then mu + KUSERMAP else mu) <= mu + KUSERMAP) by (destruct (mu <? au + m * csize c); (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia).
          pose proof (MONO _ _ PM). lia.
        * (* [comment removed for export] *)
          rewrite S0R. fold r mfa nf. (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). fold mu au.
          destruct (mu <? au + m * csize c) eqn:WK; [| exact EF].
          exfalso. apply Z.ltb_lt in WK. exact (NU eq_refl (UX (or_intror eq_refl) WK)).
  Qed.
End HN.
End WithCeil.
End AsAllocMHoleN.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMRunPf.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocM3p.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Section RUNPF.
  Variables (mem MP : word -> option byte) (r2 : bvmap 5 word) (S : word) (n : Z) (x18 x19 x22 x23 x24 x25 x26 x27 : word).
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  Hypothesis Pfoot : forall x : word, MP x <> mem x -> (U S - 2272 <= U x < U S)%Z.
  Hypothesis Pgrows : mem_grows mem MP.
  #[local] Abbreviation MA := (ma_A MP S n x18 x19 x22 x23 x24 x25 x26 x27).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation MF := (amh_mem ARB r2 MA sp2).

  Lemma mf_G1 : (2 ^ 32 + 48 <= U sp2)%Z /\ (U sp2 + 16 <= 2 ^ 47)%Z.
  Proof using GS. pose proof (u64_range S). rewrite at_u by lia. lia. Qed.

  Lemma mf_MA : forall x : word, (U x < U S - 2320 \/ U S - 2272 <= U x)%Z -> MF x = MA x.
  Proof using GS. intros x Hx. pose proof (u64_range S). apply (amh_mem_outside ARB r2 MA sp2 mf_G1). rewrite at_u by lia. lia. Qed.

  Lemma mf_above : forall x : word, (U S - 2128 <= U x)%Z -> MF x = MP x.
  Proof using GS. intros x Hx. rewrite mf_MA by lia. apply (ma_A_outside MP S n x18 x19 x22 x23 x24 x25 x26 x27 GS). lia. Qed.

  Lemma mf_outside : forall x : word, (U x < U S - 2320 \/ U S <= U x)%Z -> MF x = mem x.
  Proof using Pfoot GS.
    intros x Hx. rewrite mf_MA by lia. rewrite (ma_A_outside MP S n x18 x19 x22 x23 x24 x25 x26 x27 GS) by lia.
    destruct (decide (MP x = mem x)) as [E | NE]; [exact E|]. pose proof (Pfoot x NE). lia.
  Qed.

  Lemma mf_grows : mem_grows mem MF.
  Proof using Pgrows. eapply mem_grows_trans; [exact Pgrows|]. eapply mem_grows_trans; [apply ma_A_grows | apply amh_mem_grows]. Qed.

  (* [comment removed for export] *)
  Lemma mf_rd_above : forall (k : Z) (w : nat) (bs : list byte), (-2128 <= k)%Z -> (k + Z.of_nat w <= 0)%Z ->
    rdn ASEGS MP (at_ S k) w = Some bs -> rdn ASEGS MF (at_ S k) w = Some bs.
  Proof using GS.
    intros k w bs K1 K2 Hr. pose proof (u64_range S). destruct GS as [G1 G2]. rewrite <- Hr.
    apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply mf_above. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mf_slotsA : forall (k : Z) (v : word), In (k, v) (ma_slotsA S n x18 x19 x22 x23 x24 x25 x26 x27) ->
    rdn ASEGS MF (at_ S k) 8 = Some (LE8 v).
  Proof using Gn GS.
    intros k v Hin. pose proof (u64_range S). pose proof GS as [G1 G2].
    pose proof (ma_slotsA_range S n x18 x19 x22 x23 x24 x25 x26 x27 k v Hin) as [Hk1 Hk2].
    pose proof (rzn_range n Gn) as RZ. pose proof (needed_rz n Gn) as NR. pose proof (cofn_range n Gn) as CR.
    set (m0 := Z_to_bv 64 AIMGHI : word).
    assert (Um0 : U m0 = AIMGHI) by ((lazymatch goal with |- ?G => let G' := eval unfold m0 in G in change_no_check G' end); unorm; reflexivity).
    assert (GT0 : (4096 <= 4096 /\ 4096 + 4096 <= U S - 3584)%Z) by lia.
    assert (Gm0 : (AIMGHI <= U m0 /\ U m0 + needed n <= U S - 3584)%Z) by (rewrite Um0; lia).
    rewrite <- (ma_P2_slotsA MP S 4096 n 1 (Z_to_bv 64 0) (Z_to_bv 64 0) m0 (Z_to_bv 8 0) x18 x19 x22 x23 x24 x25 x26 x27 GS GT0 Gn Gm0 k v Hin).
    apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
    rewrite mf_MA by lia. symmetry.
    rewrite (ma_P2_outside MP S 4096 n 1 (Z_to_bv 64 0) (Z_to_bv 64 0) m0 (Z_to_bv 8 0) x18 x19 x22 x23 x24 x25 x26 x27 GS Gn Gm0) by (rewrite Um0; lia).
    apply (ma_B_outside MP S 4096 n 1 (Z_to_bv 64 0) (Z_to_bv 64 0) x18 x19 x22 x23 x24 x25 x26 x27 GS GT0 Gn); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mf_cb_slots : forall (o : Z) (v : word),
    In (o, v) [(-8, at_ ARB 0x4bdc4); (-16, getr r2 8); (-24, getr r2 9); (-32, getr r2 18); (-40, getr r2 19); (-48, getr r2 20)]%Z ->
    rdn ASEGS MF (at_ sp2 o) 8 = Some (LE8 v).
  Proof using GS. intros o v Hin. exact (amh_mem_slots ASEGS ARB r2 MA sp2 mf_G1 o v Hin). Qed.
End RUNPF.
End FPGen.
End AsAllocMRunPf.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocM3n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocM3p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocMRunP AsAllocMRunPf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMMemAm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHypR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvOpsCI3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg AsAllocM8Lf AsAllocM8Li AsAllocM8Lj AsAllocM8Lq AsAllocM8Ls AsAllocM8Lt.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

From Stdlib Require Import FunctionalExtensionality.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod4096_mod8p : forall t, t mod 4096 = 0 -> t mod 8 = 0.
Proof. intros t Ht. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma restrict_mkst_p : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma store_ok1_defP : forall (m : mem) (a : word), m a <> None -> store_ok ASEGS m a 1%nat = true.
Proof.
  intros m a D. apply store_ok_of_all; [pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  intros x Hx. assert (x = a) by (apply bv_eq; cbn in Hx; lia). subst x. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (m a); [discriminate | exact (False_ind _ (D eq_refl))].
Qed.

Section WithCeil.
Context {RC : run_ceil}.

Section TOPP1.
  Variable bt : as_boot.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis HTP : TP = ia_tp asan_addrs.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  Definition at_refill_ret (fx : FPState) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (n : Z) (st' : ast) (res : Z)
             (c' : config) : Prop :=
    exists (rq : bvmap 5 word) (Mq : mem) (mdlq : Model) (x18 x19 : word) (sz : Z) (bsz : list byte),
      let S := getr R 2 in
      let c := class_of (needed n) in
      c' = mkCfg (@mkst fx rq (Z_to_bv 64 0x5052c) Mq (seg_rom ASEGS)) mdlq
      /\ m_halted mdlq = None /\ BackingAlgebra.model_ivs_wf mdlq
      /\ WF bt st' Lc FF /\ Rep bt st' Lc FF Mq mdlq
      /\ getr rq 10 = Z_to_bv 64 res /\ getr rq 2 = at_ S (-2320) /\ getr rq 8 = Z_to_bv 64 c /\ getr rq 9 = at_ (Z_to_bv 64 T) (208 + 80 * c)
      /\ getr rq 18 = Z_to_bv 64 8 /\ getr rq 19 = at_ (Z_to_bv 64 T) 208 /\ getr rq 20 = Z_to_bv 64 0x103f18 /\ getr rq 21 = Z_to_bv 64 n
      /\ getr rq 22 = Z_to_bv 64 0x103f18 /\ getr rq 23 = at_ S (-2128) /\ getr rq 24 = Z_to_bv 64 18446744073709551608
      /\ getr rq 25 = Z_to_bv 64 7 /\ getr rq 26 = Z_to_bv 64 T /\ getr rq 27 = Z_to_bv 64 1
      /\ getr rq 4 = getr R 4 /\ getr rq 3 = getr R 3
      /\ (forall (k0 : Z) (v : word), In (k0, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
             rdn ASEGS Mq (at_ S k0) 8 = Some (LE8 v))
      /\ (forall (k0 : Z) (v : word),
             In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
             rdn ASEGS Mq (at_ S k0) 8 = Some (LE8 v))
      /\ rdn ASEGS Mq (at_ S (-2120)) 4 = Some (LE4 sz) /\ rdn ASEGS Mq (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat /\ (1 <= sz <= 8 /\ bytes_le_to_Z bsz = sz)
      /\ rdn ASEGS Mq (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))
      /\ (forall (o : Z) (v : word),
             In (o, v) [(-8, at_ ARB 0x4bdc4); (-16, Z_to_bv 64 1); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (needed n)); (-48, Z_to_bv 64 (rz n))]%Z ->
             rdn ASEGS Mq (at_ (at_ S (-2272)) o) 8 = Some (LE8 v))
      /\ (forall a : word, U S - MSTK_A <= U a < U S -> Mq a <> None /\ store_ok ASEGS Mq a 1%nat = true)
      /\ (forall a : word, Mq a <> M a ->
             ((U S - 2992 <= U a < U S) \/ rt_priv (bt_ia bt) Lc FF (U a)) /\ (res = 1 -> Mq a <> None))
      /\ same_except_vm mdl mdlq /\ lazy_kept (bt_ia bt) Lc FF mdl mdlq.

  (* [comment removed for export] *)
  Theorem malloc_to_refill_ret_x :
    forall (ex : bool) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (ret sp n : Z) (st : ast) (Qok Qf : config -> Prop),
      m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> a_kact st <= KCAP -> mu_room st ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A -> U (getr R 10) = n -> 1 <= n <= 64512 -> fpc M (U (getr R 8)) sp DMAX ->
      a_cache st (class_of (needed n)) = [] ->
      (ex = true -> Z.of_nat (length (r_free (a_reg st (class_of (needed n))))) < cache_hint (class_of (needed n)) /\ utest_x st (class_of (needed n))) ->
      (forall st' c', refill_ok_st bt st (class_of (needed n)) st' -> a_cache st' (class_of (needed n)) <> [] ->
                      at_refill_ret fx R M mdl Lc FF n st' 1 c' -> katwD ASEGS c' Qok Qf) ->
      (forall st' c', refill_fail_st bt st (class_of (needed n)) st' -> at_refill_ret fx R M mdl Lc FF n st' 0 c' -> katD ASEGS c' Qf) ->
      (if ex then katsD ASEGS (cfg ASEGS fx R (ia_malloc asan_addrs) M mdl) Qok Qf else katwD ASEGS (cfg ASEGS fx R (ia_malloc asan_addrs) M mdl) Qok Qf).
  Proof using HTP BOOTG GEOM PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros ex fx R M mdl Lc FF ret sp n st Qok Qf HH MW W RP KC MUR CP HR10 Hn FPC HC0 EXH CONT1 CONT0.
    pose proof ceil_rng as CR. pose proof ceil_pg as CPG.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    set (c := class_of (needed n)) in *.
    assert (HC0' : a_cache st (rk_c n) = []) by ((lazymatch goal with |- ?G => let G' := eval unfold rk_c in G in change_no_check G' end); exact HC0).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. pose proof CP4 as CP4'. rewrite <- HTP in CP4.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx
                      & CELL_rss & CELL_lmag & CELL_tbl2 & CELL_t16 & CELL_t2048 & CELL_minrz & CELL_maxrz & CELL_maxsz & CELL_sbeg
                      & CELL_cpm & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he & CELL_gfl & CELL_pp & CELL_mfs & CELL_fill
                      & CELL_grm & CELL_rm & CELL_glsn & CELL_lsn & CELL_magic & CELL_hook & CELL_thr64 & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9).
    pose proof GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _ & OBL_rt_private & _).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_rt_private_stmt in OBL_rt_private.
    pose proof (mc_needed n Hn) as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6 & NF7 & NF8). fold c in NF3, NF4.
    pose proof (rk_cells bt st Lc FF M mdl n W RP Hn HC0') as (Pcnt0 & _ & _ & _ & _ & _ & _ & _ & TW0). unfold rk_c in Pcnt0. fold c in Pcnt0.
    pose proof (rk_geom bt st Lc FF n W Hn) as (SB0 & SB16 & SBH & SBC & TS & CS & _).
    hidehyp GCT.
    (* [comment removed for export] *)
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & _ & SB1). hidehyp GCB.
    hidehyp GTB.
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi asan_addrs] in GTI, GCI.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, KSPACE, NMAX in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st Lc FF M mdl z W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - Hz. am_tauto. }
    destruct R14 as (Bw1 & Bw2 & Bw3 & Bw4 & Bw5).
    set (Mr := mrestrict Hd M).
    Ltac hoff NH := apply hid_off_of; intros z Hz; unfold T_UNW, T_QC, T_PC, PC_SZ in *; split; [lia | apply NH; lia].
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    (* [comment removed for export] *)
    assert (K_mcs : rdn ASEGS Mr (Z_to_bv 64 0x10827c) 4 = Some (LE4 30)) by konst Hd M R1 NHs CELL_mcs.
    assert (K_gcf : rdn ASEGS Mr (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8))) by konst Hd M R1 NHs CELL_gcf.
    assert (K_fum : rdn ASEGS Mr (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_fum.
    assert (K_inited : rdn ASEGS Mr (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_inited.
    assert (K_pg : rdn ASEGS Mr (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP))) by konst Hd M R1 NHs CELL_pg.
    assert (K_P : rdn ASEGS Mr (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096))) by konst Hd M R1 NHs CELL_P.
    assert (K_kif : rdn ASEGS Mr (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_kif.
    assert (K_key : rdn ASEGS Mr (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 0x106de0) 4) with (Z_to_bv 64 0x106de4 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_key. }
    assert (K_tsdp : rdn ASEGS Mr (at_ tp (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by (rewrite CP4; wd_ulia_c); rewrite CP4; wd_ulia_c). konst Hd M R1 NHs CELL_tsdp. }
    assert (K_tctx : rdn ASEGS Mr (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))) by konst Hd M R1 NHs CELL_tctx.
    assert (K_rss : rdn ASEGS Mr (Z_to_bv 64 0x1897e2) 1 = Some [Z_to_bv 8 0]) by konst Hd M R1 NHs CELL_rss.
    assert (K_lmag : rdn ASEGS Mr (Z_to_bv 64 0x10490) 8 = Some (LE8 MAGICw)).
    { (lazymatch goal with |- ?G => let G' := eval unfold MAGICw in G in change_no_check G' end). konst Hd M R1 NHs CELL_lmag. }
    assert (K_tbl2 : rdn ASEGS Mr (at_ (Z_to_bv 64 0x10500) 4) 1 = Some [Z_to_bv 8 3]).
    { replace (at_ (Z_to_bv 64 0x10500) 4) with (Z_to_bv 64 0x10504 : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_tbl2. }
    assert (K_t16 : rdn ASEGS Mr (at_ (Z_to_bv 64 0x10600) 8) 1 = Some [Z_to_bv 8 4]).
    { replace (at_ (Z_to_bv 64 0x10600) 8) with (Z_to_bv 64 0x10608 : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_t16. }
    assert (K_t2048 : rdn ASEGS Mr (at_ (Z_to_bv 64 0x10600) 49) 1 = Some [Z_to_bv 8 11]).
    { replace (at_ (Z_to_bv 64 0x10600) 49) with (Z_to_bv 64 0x10631 : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_t2048. }
    assert (K_minrz : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 3624) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 16))).
    { replace (at_ (Z_to_bv 64 0x103f18) 3624) with (Z_to_bv 64 0x104d40 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_minrz. }
    assert (K_maxrz : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 3626) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 2048))).
    { replace (at_ (Z_to_bv 64 0x103f18) 3626) with (Z_to_bv 64 0x104d42 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_maxrz. }
    assert (K_maxsz : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40)))).
    { replace (at_ (Z_to_bv 64 0x103f18) 3616) with (Z_to_bv 64 0x104d38 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_maxsz. }
    assert (K_sbeg : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 32) 8 = Some (LE8 (Z_to_bv 64 SBEG))).
    { replace (at_ (Z_to_bv 64 0x103f18) 32) with (Z_to_bv 64 0x103f38 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_sbeg. }
    (* [comment removed for export] *)
    Ltac thr_cell Hd M NHrt C := apply (cellZ_restrict Hd M _ _ _ C); [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW, T_QC, T_PC, PC_SZ in G in change_no_check G' end); lia | unfold T_UNW, T_QC, T_PC, PC_SZ in *; lia | hoff NHrt].
    assert (K_thr : rdn ASEGS Mr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tback. }
    assert (K_T0 : rdn ASEGS Mr (Z_to_bv 64 T) 8 = Some (LE8 (Z_to_bv 64 CTX))) by thr_cell Hd M NHrt Tctx.
    assert (K_tid : rdn ASEGS Mr (at_ (Z_to_bv 64 CTX) 8) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 CTX) 8) with (Z_to_bv 64 (CTX + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttid. }
    assert (K_unw : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tunw. }
    assert (K_sw : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 40) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 40) with (Z_to_bv 64 (T + 40)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tsw. }
    assert (K_top : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 8) 8 = Some (LE8 (Z_to_bv 64 (bt_stack_top bt)))).
    { replace (at_ (Z_to_bv 64 T) 8) with (Z_to_bv 64 (T + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttop. }
    assert (K_bot : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 16) 8 = Some (LE8 (Z_to_bv 64 (bt_stack_bottom bt)))).
    { replace (at_ (Z_to_bv 64 T) 16) with (Z_to_bv 64 (T + 16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tbot. }
    assert (K_cnt0 : rdn ASEGS Mr (at_ (Z_to_bv 64 T) (208 + 80 * c)) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 T) (208 + 80 * c)) with (Z_to_bv 64 (T + T_PC + PC_SZ * c)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Pcnt0. }
    (* [comment removed for export] *)
    assert (SOKstk : store_ok ASEGS Mr (at_ S (-3584)) 3584 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. apply CPstk. cbn in Hx. lia. }
    assert (SOKT : store_ok ASEGS Mr (Z_to_bv 64 T) 4096 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ TW); wd_ulia_c. }
    assert (FPCr : fpc Mr (U (getr R 8)) (U S) DMAX).
    { rewrite CP2. apply (fpc_kept_gen M _ _ _ FPC Mr). destruct (fpc_shape _ _ _ _ FPC) as [ST|FR]; [left; exact ST | right].
      intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. apply NHs; unfold PTRHI in *; lia. }
    (* [comment removed for export] *)
    assert (En : getr R 10 = Z_to_bv 64 n) by (rewrite <- HR10; symmetry; apply Z_to_bv_bv_unsigned).
    destruct (run_mA_pre Mr (seg_rom ASEGS) R S ra0 tp (Z_to_bv 64 TSDP) (Z_to_bv 64 PGP) (Z_to_bv 64 (bt_stack_top bt)) (Z_to_bv 64 (bt_stack_bottom bt))
                T CTX n SBEG 0 DMAX eq_refl eq_refl eq_refl En)
      as (r2 & r3 & MP & sz & bsz & x18 & x19 & URUN).
    all: fold c.
    all: try assumption.
    all: try (wd_ulia_c).
    all: try (rewrite CP4; wd_ulia_c).
    all: try (lazymatch goal with |- _ \/ _ => rewrite ?CP2; unfold hide in *; unfold PG in *; lia end).
    all: try (rewrite CP2; split; [lia|]; split; [lia | apply mod4096_mod8p; exact TPG]).
    all: try (lazymatch goal with |- _ /\ _ => rewrite ?CP2; unfold hide in *; unfold PG in *; lia end).
    all: let k := numgoals in guard k = 1.
    clear K_mcs K_gcf K_fum K_inited K_pg K_P K_kif K_key K_tsdp K_tctx K_rss K_lmag K_tbl2 K_t16 K_t2048 K_minrz K_maxrz K_maxsz K_sbeg.
    cbn zeta in URUN. fold c in URUN.
    destruct URUN as (RUN & A1 & A2 & A10 & A11 & A12 & A13 & A8 & A9 & A18 & A19 & A20 & A26 & AK
                      & B2 & B3 & B4 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B27
                      & SZ1 & SZ2 & FOOTP & GRP & Psz4 & Psz8 & Lsz & Ptr & Pslots).
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite CP2; lia).
    pose proof (mf_outside Mr MP r2 S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm FOOTP) as MFO.
    pose proof (mf_grows Mr MP r2 S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GRP) as MFG.
    pose proof (mf_slotsA MP r2 S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm Hn) as MFS.
    pose proof (mf_rd_above MP r2 S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm) as MFR.
    pose proof (mf_cb_slots MP r2 S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm) as MFC.
    set (MA := ma_A MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) in *.
    set (MF := amh_mem ARB r2 MA (at_ S (-2272))) in *.
    clearbody MF. clear MA.
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end). replace (Z_to_bv 64 (ia_malloc asan_addrs)) with (Z_to_bv 64 0x6e4cc : word) by (apply bv_eq; reflexivity).
    assert (LIFT : (forall mdl1, MInv (a_aa st) mdl1 -> same_but_materialized mdl mdl1 -> hclean Hd (@mkst fx r3 (Z_to_bv 64 0x509cc) MF (seg_rom ASEGS)) ->
                      if ex then katsD ASEGS (mkCfg (unrestrict Hd (ms_mem (@mkst fx R (Z_to_bv 64 0x6e4cc) M (seg_rom ASEGS))) (@mkst fx r3 (Z_to_bv 64 0x509cc) MF (seg_rom ASEGS))) mdl1) Qok Qf
                      else katwD ASEGS (mkCfg (unrestrict Hd (ms_mem (@mkst fx R (Z_to_bv 64 0x6e4cc) M (seg_rom ASEGS))) (@mkst fx r3 (Z_to_bv 64 0x509cc) MF (seg_rom ASEGS))) mdl1) Qok Qf) ->
                   if ex then katsD ASEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x6e4cc) M (seg_rom ASEGS)) mdl) Qok Qf
                   else katwD ASEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x6e4cc) M (seg_rom ASEGS)) mdl) Qok Qf).
    { intros KONT. destruct ex.
      - apply (katsD_msteps_acct ASEGS Hd (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
                 (@mkst fx R (Z_to_bv 64 0x6e4cc) M (seg_rom ASEGS)) (@mkst fx r3 (Z_to_bv 64 0x509cc) MF (seg_rom ASEGS)) mdl);
          [apply lazy_cover_HID | exact Bw1 | exact Bw2 | exact HH | rewrite restrict_mkst_p; exact RUN | exact KONT].
      - apply (katwD_msteps_acct ASEGS Hd (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
                 (@mkst fx R (Z_to_bv 64 0x6e4cc) M (seg_rom ASEGS)) (@mkst fx r3 (Z_to_bv 64 0x509cc) MF (seg_rom ASEGS)) mdl);
          [apply lazy_cover_HID | exact Bw1 | exact Bw2 | exact HH | rewrite restrict_mkst_p; exact RUN | exact KONT]. }
    apply LIFT. clear LIFT.
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x6e4cc) M (seg_rom ASEGS))) with M by reflexivity.
    set (M1 := munrestrict Hd M MF).
    (* [comment removed for export] *)
    assert (VISstk : forall a : word, U S - 3584 <= U a < U S -> M1 a = MF a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply munrestrict_off. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply NHs; [pose proof (u64_range a); lia | left; rewrite CP2 in Ha; lia]. }
    assert (OUT1 : forall a : word, M1 a <> M a -> U S - 2320 <= U a < U S).
    { intros a NE. unfold M1, munrestrict in NE. destruct (Hd a) eqn:Eh; [exfalso; exact (NE eq_refl)|].
      assert (EMr : Mr a = M a) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Eh).
      destruct (Z_lt_le_dec (U a) (U S - 2320)) as [L|L]; [exfalso; apply NE; rewrite <- EMr; apply MFO; left; exact L|].
      destruct (Z_lt_le_dec (U a) (U S)) as [L2|L2]; [lia | exfalso; apply NE; rewrite <- EMr; apply MFO; right; exact L2]. }
    assert (GRin : mem_grows M M1).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex; [exact Hx|].
      apply MFG. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by exact Ex. exact Hx. }
    assert (M1def : forall a : word, M1 a <> M a -> M1 a <> None).
    { intros a NE. destruct (M1 a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (M a) eqn:E2; [|reflexivity].
      exfalso. assert (X : M a <> None) by (rewrite E2; discriminate). apply GRin in X. rewrite E1 in X. exact (X eq_refl). }
    assert (STK1 : forall a : word, U S - 3584 <= U a < U S -> M1 a <> None /\ store_ok ASEGS M1 a 1%nat = true).
    { intros a Ha. split.
      - apply GRin. apply store_ok1_heap; [lia|]. apply CPstk. rewrite <- CP2. lia.
      - eapply store_ok_mono; [exact GRin|]. apply CPstk. rewrite <- CP2. lia. }
    assert (RX1 : RepX bt (fun _ : Z => False) st Lc FF M1 mdl1).
    { apply (repx_frame_step bt (fun _ : Z => False) st Lc FF M M1 mdl mdl1 W).
      - exists M. split; [exact RP | intros a NE; exfalso; exact (NE eq_refl)].
      - intros a NE. split; [| exact (M1def a NE)]. intros RCa.
        pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa) as LT. pose proof (OUT1 a NE) as O. rewrite CP2 in O. lia.
      - exact MI1.
      - exact SBM1. }
    (* [comment removed for export] *)
    assert (RD1 : forall (k : Z) (w : nat) (bs : list byte), -3584 <= k -> k + Z.of_nat w <= 0 -> rdn ASEGS MF (at_ S k) w = Some bs -> rdn ASEGS M1 (at_ S k) w = Some bs).
    { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply VISstk. lia. }
    assert (FA1 : forall (k0 : Z) (v : word), In (k0, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
              rdn ASEGS M1 (at_ S k0) 8 = Some (LE8 v)).
    { intros k0 v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k0 v Hin) as [Hk1 Hk2].
      apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. exact (MFS k0 v Hin). }
    assert (FI1 : forall (k0 : Z) (v : word),
              In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn ASEGS M1 (at_ S k0) 8 = Some (LE8 v)).
    { intros k0 v Hin.
      assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (Pslots k0 v Hin)]. }
    assert (FS41 : rdn ASEGS M1 (at_ S (-2120)) 4 = Some (LE4 sz)) by (apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]; apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Psz4]).
    assert (FS81 : rdn ASEGS M1 (at_ S (-2120)) 8 = Some bsz) by (apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]; apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Psz8]).
    assert (FTR1 : rdn ASEGS M1 (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))) by (apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]; apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Ptr]).
    assert (FC1 : forall (o : Z) (v : word),
              In (o, v) [(-8, at_ ARB 0x4bdc4); (-16, Z_to_bv 64 1); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (needed n)); (-48, Z_to_bv 64 (rz n))]%Z ->
              rdn ASEGS M1 (at_ (at_ S (-2272)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at.
      apply (MFC o v). rewrite B8, B9, B18, B19, B20. exact Hin. }
    (* [comment removed for export] *)
    set (spR := at_ S (-2320)). set (raR := Z_to_bv 64 0x5052c : word).
    assert (UspR : U spR = U S - 2320) by ((lazymatch goal with |- ?G => let G' := eval unfold spR in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (E4 : getr r3 4 = tp) by (rewrite (AK 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact B4).
    assert (E3 : getr r3 3 = getr R 3) by (rewrite (AK 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact B3).
    assert (HL1 : m_halted mdl1 = None) by exact (halted_sbm mdl mdl1 SBM1 HH).
    assert (MW1 : BackingAlgebra.model_ivs_wf mdl1) by exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW).
    (* [comment removed for export] *)
    assert (TRANS : forall (res : Z) (st' : ast) (r' : bvmap 5 word) (M' : mem) mdl',
              WF bt st' Lc FF -> RepX bt (fun _ : Z => False) st' Lc FF M' mdl' ->
              same_except_vm mdl1 mdl' -> lazy_kept (bt_ia bt) Lc FF mdl1 mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
              (forall a : word, M' a <> M1 a -> refill0_foot bt st c (U spR) (U a) /\ (res = 1 -> M' a <> None) /\ (M' a <> None \/ pop_zone_t bt st c (U a))) ->
              getr r' 10 = Z_to_bv 64 res -> getr r' 2 = spR -> getr r' 8 = getr r3 8 -> getr r' 9 = getr r3 9 ->
              s_regs r' (getr r3 18) (getr r3 19) (getr r3 20) (getr r3 21) (getr r3 22) (getr r3 23) (getr r3 24) (getr r3 25) (getr r3 26) (getr r3 27) ->
              getr r' 4 = tp -> getr r' 3 = getr R 3 ->
              at_refill_ret fx R M mdl Lc FF n st' res (mkCfg (@mkst fx r' raR M' (seg_rom ASEGS)) mdl')).
    { intros res st' r' M' mdl' W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q8 Q9 QS Q4 Q3.
      destruct RX' as (M0 & RP' & DX).
      assert (EM : M' = M0).
      { apply functional_extensionality. intros a. destruct (decide (M' a = M0 a)) as [E|NE]; [exact E | destruct (DX a NE) as [[] _]]. }
      subst M0.
      destruct QS as (S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27).
      (* [comment removed for export] *)
      assert (KEEP : forall x : word, U S - 2320 <= U x < U S -> M' x = M1 x).
      { intros x Hx. destruct (decide (M' x = M1 x)) as [E|NE]; [exact E | exfalso]. destruct (FOOT x NE) as [F _].
        destruct (refill0_foot_lt bt st Lc FF c (U spR) (U x) W NF3 F) as [L | L]; [rewrite UspR in L; lia | rewrite CP2 in Hx; lia]. }
      assert (RDq : forall (k : Z) (w : nat) (bs : list byte), -2320 <= k -> k + Z.of_nat w <= 0 -> rdn ASEGS M1 (at_ S k) w = Some bs -> rdn ASEGS M' (at_ S k) w = Some bs).
      { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply KEEP. lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold at_refill_ret in G in change_no_check G' end). exists r', M', mdl', x18, x19, sz, bsz. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S c. (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end).
      split; [reflexivity|]. split; [exact HL'|]. split; [exact MW'|]. split; [exact W'|]. split; [exact RP'|].
      split; [exact Q10|]. split; [exact Q2|]. split; [rewrite Q8; exact A8|].
      split; [rewrite Q9; exact A9|]. split; [rewrite S18; exact A18|]. split; [rewrite S19; exact A19|]. split; [rewrite S20; exact A20|].
      split; [rewrite S21, (AK 21%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact B21|]. split; [rewrite S22, (AK 22%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact B22|].
      split; [rewrite S23, (AK 23%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact B23|]. split; [rewrite S24, (AK 24%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact B24|].
      split; [rewrite S25, (AK 25%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact B25|]. split; [rewrite S26; exact A26|].
      split; [rewrite S27, (AK 27%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact B27|].
      split; [exact Q4|]. split; [exact Q3|].
      split. { intros k0 v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k0 v Hin) as [Hk1 Hk2]. apply RDq; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FA1 k0 v Hin)]. }
      split. { intros k0 v Hin.
               assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
               apply RDq; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FI1 k0 v Hin)]. }
      split; [apply RDq; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS41]|]. split; [apply RDq; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS81]|]. split; [exact Lsz|]. split; [split; [clear - SZ1 SZ2; change (Z.of_nat DMAX) with 6 in SZ2; lia | exact (proj2 SZ1)]|].
      split; [apply RDq; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FTR1]|].
      split. { intros o v Hin.
               assert (Ho : -48 <= o <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
               rewrite at_at. apply RDq; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FC1 o v Hin). }
      split. { intros a Ha.
               assert (D : M' a <> None).
               { destruct (decide (M' a = M1 a)) as [E|NE]; [rewrite E; exact (proj1 (STK1 a Ha))|].
                 destruct (FOOT a NE) as (_ & _ & [Dd | PZ]); [exact Dd | exfalso].
                 destruct (pop_zone_t_priv bt st Lc FF c (U a) W NF3 PZ) as (LT & _). rewrite CP2 in Ha. lia. }
               split; [exact D | exact (store_ok1_defP M' a D)]. }
      split. { intros a NE. destruct (decide (M' a = M1 a)) as [E|NE1].
               - rewrite E in NE |- *. split; [left; pose proof (OUT1 a NE); lia | intros _; exact (M1def a NE)].
               - destruct (FOOT a NE1) as (F & Dd & _). split; [| exact Dd].
                 destruct (refill0_foot_priv bt st Lc FF c (U spR) (U a) W NF3 F) as [L | L]; [left; rewrite UspR in L; lia | right; exact L]. }
      split; [eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
      intros a Ha. rewrite (LK a Ha). exact (lazy_kept_sbm bt Lc FF mdl mdl1 SBM1 a Ha). }
    replace (Z_to_bv 64 0x509cc : word) with (0x509cc%bv : word) by (apply bv_eq; reflexivity).
    destruct ex.
    { destruct (EXH eq_refl) as [ENF EUX].
    apply (@refill_katsD_b RC fx bt BT_segs BT_ia BOOTG TP TSDP PGP FL MIDEND CELLS
             PCELLS (fun _ : Z => False) c st Lc FF M1 (seg_rom ASEGS) mdl1 r3 spR raR tp (getr R 3) Qok Qf NF3 W RX1 HL1 MW1 HC0 KC MUR ENF EUX).
    - intros z [].
    - exact A1.
    - exact A2.
    - exact E4.
    - exact E3.
    - rewrite CP4', HTP. reflexivity.
    - rewrite A10. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC in G in change_no_check G' end). unorm. lia.
    - rewrite A11. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ in G in change_no_check G' end). unorm. lia.
    - exact A12.
    - exact A13.
    - rewrite UspR, CP2. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - intros i Hi. rewrite UspR in Hi.
      assert (Ui : U (Z_to_bv 64 i) = i) by (wd_ulia).
      apply STK1. rewrite Ui. lia.
    - (* [comment removed for export] *)
      intros st' r' M' mdl' EST W' RX' CNE SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
      apply (CONT1 st' _ EST CNE).
      apply (TRANS 1 st' r' M' mdl' W' RX' SEV LK MW' HL'); try assumption.
      intros a Ha. destruct (FOOT a Ha) as [F Dd]. split; [exact F | split; [intros _; exact Dd | left; exact Dd]].
    - (* [comment removed for export] *)
      intros st' r' M' mdl' EST W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
      apply (CONT0 st' _ EST).
      apply (TRANS 0 st' r' M' mdl' W' RX' SEV LK MW' HL'); try assumption.
      intros a Ha. destruct (FOOT a Ha) as [F DZ]. split; [exact F | split; [intros E01; discriminate E01 | exact DZ]]. }
    { apply (@refill_katwD_b RC fx bt BT_segs BT_ia BOOTG TP TSDP PGP FL MIDEND CELLS
             PCELLS (fun _ : Z => False) c st Lc FF M1 (seg_rom ASEGS) mdl1 r3 spR raR tp (getr R 3) Qok Qf NF3 W RX1 HL1 MW1 HC0 KC MUR).
    - intros z [].
    - exact A1.
    - exact A2.
    - exact E4.
    - exact E3.
    - rewrite CP4', HTP. reflexivity.
    - rewrite A10. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC in G in change_no_check G' end). unorm. lia.
    - rewrite A11. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ in G in change_no_check G' end). unorm. lia.
    - exact A12.
    - exact A13.
    - rewrite UspR, CP2. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - intros i Hi. rewrite UspR in Hi.
      assert (Ui : U (Z_to_bv 64 i) = i) by (wd_ulia).
      apply STK1. rewrite Ui. lia.
    - (* [comment removed for export] *)
      intros st' r' M' mdl' EST W' RX' CNE SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
      apply (CONT1 st' _ EST CNE).
      apply (TRANS 1 st' r' M' mdl' W' RX' SEV LK MW' HL'); try assumption.
      intros a Ha. destruct (FOOT a Ha) as [F Dd]. split; [exact F | split; [intros _; exact Dd | left; exact Dd]].
    - (* [comment removed for export] *)
      intros st' r' M' mdl' EST W' RX' SEV LK MW' HL' FOOT Q10 Q2 Q1 Q8 Q9 QS Q4 Q3.
      apply (CONT0 st' _ EST).
      apply (TRANS 0 st' r' M' mdl' W' RX' SEV LK MW' HL'); try assumption.
      intros a Ha. destruct (FOOT a Ha) as [F DZ]. split; [exact F | split; [intros E01; discriminate E01 | exact DZ]]. }
  Qed.

  (* [comment removed for export] *)
  Theorem malloc_to_refill_ret :
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (ret sp n : Z) (st : ast) (Qok Qf : config -> Prop),
      m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> a_kact st <= KCAP -> mu_room st ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A -> U (getr R 10) = n -> 1 <= n <= 64512 -> fpc M (U (getr R 8)) sp DMAX ->
      a_cache st (class_of (needed n)) = [] ->
      (forall st' c', refill_ok_st bt st (class_of (needed n)) st' -> a_cache st' (class_of (needed n)) <> [] ->
                      at_refill_ret fx R M mdl Lc FF n st' 1 c' -> katwD ASEGS c' Qok Qf) ->
      (forall st' c', refill_fail_st bt st (class_of (needed n)) st' -> at_refill_ret fx R M mdl Lc FF n st' 0 c' -> katD ASEGS c' Qf) ->
      katwD ASEGS (cfg ASEGS fx R (ia_malloc asan_addrs) M mdl) Qok Qf.
  Proof using HTP BOOTG GEOM PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros fx R M mdl Lc FF ret sp n st Qok Qf HH MW W RP KC MUR CP HR10 Hn FPC HC0 CONT1 CONT0.
    exact (malloc_to_refill_ret_x false fx R M mdl Lc FF ret sp n st Qok Qf HH MW W RP KC MUR CP HR10 Hn FPC HC0 ltac:(intros X0; discriminate X0) CONT1 CONT0).
  Qed.
  Theorem malloc_to_refill_ret_s :
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (ret sp n : Z) (st : ast) (Qok Qf : config -> Prop),
      m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> a_kact st <= KCAP -> mu_room st ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A -> U (getr R 10) = n -> 1 <= n <= 64512 -> fpc M (U (getr R 8)) sp DMAX ->
      a_cache st (class_of (needed n)) = [] ->
      Z.of_nat (length (r_free (a_reg st (class_of (needed n))))) < cache_hint (class_of (needed n)) -> utest_x st (class_of (needed n)) ->
      (forall st' c', refill_ok_st bt st (class_of (needed n)) st' -> a_cache st' (class_of (needed n)) <> [] ->
                      at_refill_ret fx R M mdl Lc FF n st' 1 c' -> katwD ASEGS c' Qok Qf) ->
      (forall st' c', refill_fail_st bt st (class_of (needed n)) st' -> at_refill_ret fx R M mdl Lc FF n st' 0 c' -> katD ASEGS c' Qf) ->
      katsD ASEGS (cfg ASEGS fx R (ia_malloc asan_addrs) M mdl) Qok Qf.
  Proof using HTP BOOTG GEOM PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros fx R M mdl Lc FF ret sp n st Qok Qf HH MW W RP KC MUR CP HR10 Hn FPC HC0 ENF EUX CONT1 CONT0.
    exact (malloc_to_refill_ret_x true fx R M mdl Lc FF ret sp n st Qok Qf HH MW W RP KC MUR CP HR10 Hn FPC HC0 ltac:(intros _; exact (conj ENF EUX)) CONT1 CONT0).
  Qed.
End TOPP1.
End WithCeil.
