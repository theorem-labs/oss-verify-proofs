(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).



Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod4096_of_64k : forall x, x mod 2 ^ 16 = 0 -> x mod 4096 = 0.
Proof. intros x Hx. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).
  #[local] Abbreviation IA := (bt_ia bt).

  (* [comment removed for export] *)
  Definition usermap_ledger (st : ast) (c : Z) (mdl mdl' : Model) : Prop :=
    let lo := region_beg SBEG c + r_mapped_user (a_reg st c) in
    (r_uhole (a_reg st c) = false -> vm_maps (m_vmmaps mdl') = vm_maps (m_vmmaps mdl))
    /\ (r_uhole (a_reg st c) = true -> Permutation (vm_maps (m_vmmaps mdl')) ((Z_to_bv 64 lo, Z_to_bv 64 KUSERMAP) :: vm_maps (m_vmmaps mdl)))
    /\ (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + KUSERMAP))
    /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
    /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + KUSERMAP))
    /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                   /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv)))
              (m_vm_lazy mdl')
    /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
    /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
    /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl)
    /\ eager_used mdl' <= eager_used mdl + KUSERMAP.

  (* [comment removed for export] *)
  Definition N3U_stmt : Prop := forall st Lc FF M0 mdl c,
    WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_uhole (a_reg st c) = false ->
    r_mapped_user (a_reg st c) + KUSERMAP + KUSERMAP <= KREGION_EXHAUST -> BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    let lo := region_beg SBEG c + r_mapped_user (a_reg st c) in
    let addr : word := Z_to_bv 64 lo in let size : word := Z_to_bv 64 KUSERMAP in
    let A2 := a_aa st ++ [(sh_lo lo, sh_lo lo + KUSERMAP / 8)] in
    let OK := fixedin_ok_model 3 (Z_to_bv 64 50) addr size in let DS := fixedin_destroyed_model addr size in
    A_wf A2
    /\ (forall mdlm, same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
          U addr + U size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64
          /\ region_free (vm_reserved (m_vmmaps mdlm)) addr size = true /\ map_contains (vm_maps (m_vmmaps mdlm)) addr size = true
          /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true
          /\ m_halted (OK mdlm) = None /\ MInv (a_aa st) (OK mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (OK mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true)
          /\ m_halted (DS mdlm) = None /\ MInv (a_aa st) (DS mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (DS mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true))
    /\ (forall mdlm mdl4, same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl4 -> MInv (a_aa st) mdl4 -> MInv A2 mdl4)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl' ->
          usermap_ledger st c mdl mdl' /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (DS mdlm) mdl' ->
          ledger_destroyed bt mdl mdl' lo KUSERMAP /\ eager_used mdl' <= eager_used mdl
          /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None).
  Hypothesis N3U : N3U_stmt.

  Theorem popAm_katsD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v s6v tp gp : word) (req : Z) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    r_uhole (a_reg st c) = false -> a_kact st <= KCAP -> mu_room st ->
    let r := a_reg st c in let au := r_alloc_user r in let mu := r_mapped_user r in let nf := Z.of_nat (length (r_free r)) in
    let lo := region_beg SBEG c + mu in
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (lo <= z < lo + KUSERMAP) /\ ~ (sh_lo lo <= z < sh_lo lo + KUSERMAP / 8)) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 0x103f18 ->
    getr regs 11 = at_ (Z_to_bv 64 T) 2768 -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 (reginfo bt c) -> getr regs 14 = Z_to_bv 64 req ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    (CEIL + 464 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> (1 <= req /\ csize c * req <= 2 ^ 18) -> mu < au + csize c * req ->
    writableZ ASEGS M (U sp - 464) (U sp) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        let st' := add_meter (op_usermap st c) 0 [(sh_lo lo, sh_lo lo + KUSERMAP / 8)] 0 in
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a ->
            ((U sp - 464 <= U a < U sp) \/ (lo <= U a < lo + KUSERMAP) \/ (sh_lo lo <= U a < sh_lo lo + KUSERMAP / 8)
             \/ (T + 2792 <= U a < T + 2888) \/ (reginfo bt c + 48 <= U a < reginfo bt c + 56)) /\ M' a <> None) ->
        (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] ->
            rdn ASEGS M' (at_ sp k) 8 = Some (LE8 v)) ->
        pf_regs sp (reginfo bt c) SBEG c r' -> getr r' 1 = Z_to_bv 64 0x50f68 ->
        getr r' 10 = Z_to_bv 64 0x103f18 -> getr r' 11 = Z_to_bv 64 (reginfo bt c) -> getr r' 12 = Z_to_bv 64 (SBEG + c * 2 ^ 32) ->
        getr r' 13 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) -> getr r' 9 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) ->
        getr r' 19 = Z_to_bv 64 ((mu + 2 ^ 18 - au) / csize c) -> getr r' 20 = Z_to_bv 64 (mu + 2 ^ 18 - au) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' (0x4ea98%bv : word) M' rom) mdl') Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r0 r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ st' = op_uhole st c) ->
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> ((U sp - 464 <= U a < U sp) /\ M' a <> None) \/ (lo <= U a < lo + KUSERMAP)) ->
        regs_agree (fun i : reg => In i pf_clob) regs r0 -> pf_post0 sp ra s0v s1v s2v s3v s4v s5v s6v r0 r' ->
        katD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qf) ->
    katsD ASEGS (mkCfg (mkst regs (0x50dd4%bv : word) M rom) mdl) Qok Qf.
  Proof using N3U PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v s6v tp gp req Qok Qf Hc W RX HALT MW UH KC MUR r au mu nf lo XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 Hsp Hret Hreq Hmap WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14). fold mu au nf in E2, E3, E4, E7, E8, E13.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((Y1a & Y1b) & Y2 & Y3 & Y4 & _). fold r mu au in Y1a, Y1b, Y2, Y3, Y4.
    pose proof (csize_pos c Hc) as [CS1 CS2].
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CREST).
    assert (CELL_sbeg : In (0x103f38, 8%nat, SBEG) (bt_consts bt)).
    { do 12 (destruct CREST as (_ & CREST)). destruct CREST as (A1 & _). exact A1. }
    assert (G_consts : 0x10000 <= TSDP /\ TSDP + 8 <= 0x65d000 /\ 0x10000 <= PGP /\ PGP + 8 <= 0x65d000 /\ 0x10000 + 88 <= TP /\ TP + 0x40 <= 0x65d000).
    { do 32 (destruct CREST as (_ & CREST)). destruct CREST as (A1 & A2 & A3 & A4 & _ & _ & _ & A8 & A9). repeat split; assumption. }
    destruct G_consts as (Gs1 & Gs2 & Gp1 & Gp2 & Gt1 & Gt2).
    pose proof PCELLS as (PC_rel & PC_rib & PC_pre & PC_dpm & PC_lim).
    set (RIz := reginfo bt c) in *. set (rbeg := region_beg SBEG c) in *.
    assert (ERI : RIz = SBEG + KSPACE + 128 * c) by reflexivity.
    assert (ERB : rbeg = SBEG + c * 2 ^ 32) by ((lazymatch goal with |- ?G => let G' := eval unfold rbeg, region_beg, KREGION in G in change_no_check G' end); reflexivity).
    assert (ELO : lo = SBEG + c * 2 ^ 32 + mu) by ((lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end); rewrite ERB; reflexivity).
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct (R4 c Hc) as [(G0 & G8 & G16 & G24 & G32 & G40 & G48 & G56 & G68 & GW) (F1 & F2 & F3)]. fold r RIz mu au nf in G16, G32, G48, G56, GW.
    rewrite BT_segs in *. destruct R14 as (Bw1 & Bw2 & _).
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
    unfold KSPACE, PG, KUSERMAP, KREGION_EXHAUST, KFAOFF, AS_HEAPLO, AS_LO in *.
    assert (TIGHT : mu - au < csize c) by (clear - Y1b Hmap Hreq; lia).
    assert (ROOM : r_mapped_user (a_reg st c) + KUSERMAP + KUSERMAP <= KREGION_EXHAUST) by (exact (usermap_room bt st Lc FF c _ _ W Hc TIGHT)).
    assert (SLOT : SBEG <= lo /\ lo + 2 ^ 18 <= SBEG + 2 ^ 37 /\ lo mod 8 = 0 /\ lo mod 4096 = 0).
    { split; [rewrite ELO; lia|]. split; [unfold fa_beg in E5; fold rbeg in E5; rewrite ELO; rewrite ERB in E5; lia|].
      (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end). split; [apply mod8_of_4096_sum; [exact E11 | exact E13] | apply mod4096_sum; [exact E11 | exact E13]]. }
    destruct SLOT as (SL0 & SL1 & SL8 & SL4k).
    assert (SLa : 17594333495296 <= lo) by lia.
    assert (SLb : lo + 2 ^ 18 <= CEIL) by lia.
    destruct (sh_band lo (2 ^ 18) SLa ltac:(lia) SLb ltac:(reflexivity)) as (SHB0 & SHB1 & SHB2).
    unfold AS_GAPHI, AS_HEAPLO in SHB0, SHB1. replace (2 ^ 18 / 8) with (2 ^ 15) in SHB1, SHB2 by reflexivity.
    set (SH := sh_lo lo) in *. assert (ESH' : SH = SB + lo / 8) by reflexivity. rewrite <- ESH' in SHB0, SHB1, SHB2.
    assert (ESH : SH = (SBEG + c * 2 ^ 32 + mu) / 8 + 2147450880) by (rewrite ESH', ELO; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); lia).
    assert (YIMG : forall z, XL c z -> ~ (AIMGLO <= z < AIMGHI)).
    { intros z [Hx | Hl]; [exact (proj1 (proj2 (XOFF z Hx))) | fold RIz in Hl; lia]. }
    assert (YCTX : forall z, XL c z -> ~ (CTX + 152 <= z < CTX + 160)).
    { intros z [Hx | Hl]; [exact (proj1 (proj2 (proj2 (XOFF z Hx)))) | fold RIz in Hl; clear - Hl CSP ERI E9 E10 C1; lia]. }
    assert (XRI : forall i, RIz + 8 <= i < RIz + 128 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (XOFF i Hx) ltac:(fold RIz; lia)) | fold RIz in Hl; lia]. }
    assert (XSL : forall i, lo <= i < lo + 2 ^ 18 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (proj2 (proj2 (proj2 (XOFF i Hx)))) Hi) | fold RIz in Hl; lia]. }
    assert (XSH : forall i, SH <= i < SH + 2 ^ 15 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [apply (proj2 (proj2 (proj2 (proj2 (XOFF i Hx))))); fold SH; replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hi | fold RIz in Hl; lia]. }
    destruct (N3U st Lc FF M0 mdl c W RP Hc UH ROOM MW HALT KC) as (AWF2 & NODEF & BUD & LEDOK & LEDDS).
    fold r mu lo SH in AWF2, NODEF, BUD, LEDOK, LEDDS. unfold KUSERMAP in AWF2, NODEF, BUD, LEDOK, LEDDS.
    set (addr := Z_to_bv 64 lo : word) in *. set (size := Z_to_bv 64 (2 ^ 18) : word) in *.
    set (A2 := a_aa st ++ [(SH, SH + 2 ^ 18 / 8)]) in *.
    set (OKm := fixedin_ok_model 3 (Z_to_bv 64 50) addr size) in *. set (DSm := fixedin_destroyed_model addr size) in *.
    set (Hd := HID st mdl). set (Hd2 := mkH (m_vm_lazy mdl) A2).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2s : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. exact (mkH_off_zone bt BT_ia st mdl A2 z R13 Hz Hr). }
    assert (NH2ri : forall z, RIz <= z < RIz + 128 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2rt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [clear - Hz T1 T2 C1 C2 CR; lia|]. exact (pk_nolazy_rt bt st Lc FF M0 mdl W RP z Hz). }
    assert (NH2sh : forall z, SH <= z < SH + 2 ^ 15 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_allowed. (lazymatch goal with |- ?G => let G' := eval unfold A2 in G in change_no_check G' end). apply (range_allowed_last (a_aa st) SH (SH + 2 ^ 18 / 8)); [ | | lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hz].
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & AW1 & _) _]. cbn [fst] in AW1. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW1.
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & _ & AW2) _]. cbn [snd] in AW2. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW2. }
    assert (HOFF : forall (H : word -> bool) lo0 n, (forall z, lo0 <= z < lo0 + n -> H (Z_to_bv 64 z) = false) -> hid_off H lo0 n).
    { intros H lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    pose proof (pk_T_writable bt BT_segs BT_ia (XL c) st Lc FF M M0 mdl W RP D) as TWR.
    destruct (pk_junk8 M T (T + 4096) (T + 2872) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v72 & R72).
    destruct (pk_junk8 M T (T + 4096) (T + 2880) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v80 & R80).
    destruct (pk_junk8 M T (T + 4096) (T + 2792) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (vst & Rst).
    set (thr := Z_to_bv 64 T : word) in *.
    assert (UT : U thr = T) by ((lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (KC_sbeg := (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_sbeg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))). assert (KC_rel := (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_rel ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))). assert (KC_pre := (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_pre ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))).
    assert (KC_pg := (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_pg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))). assert (KC_P := (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_P ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))). assert (KC_gcf := (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_gcf ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))). assert (KC_dpm := (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_dpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))). assert (KC_lim := (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_lim ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))).
    assert (S3' : SBEG mod 4096 = 0).
    { pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16). clear - S16. exact (mod4096_of_64k _ S16). }
    apply (pf_map_arm_katsD Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx Hd2 (mkH_off_segments bt BT_ia st mdl A2 R13) A2 AWF2 (a_aa st)
             regs M rom mdl sp ra s0v s1v s2v s3v s4v s5v s6v thr tp gp (Z_to_bv 64 TSDP) (Z_to_bv 64 CTX) v72 v80 vst (Z_to_bv 64 MIDEND) (Z_to_bv 8 1)
             RIz SBEG c req au mu nf PGP 0x1990a8 T 0 Qok Qf OKm (fun m => m) DSm).
    all: try (first [exact H1 | exact H2 | exact H4 | exact H3 | exact H10 | exact H11 | exact H12 | exact H13 | exact H14 | exact H8 | exact H9 | exact H18 | exact H19 | exact H20 | exact H21 | exact H22
                    | exact Hret | exact Hc | exact Hreq | exact Hmap | exact HALT | exact Bw1 | exact Bw2]).
    - lia.
    - lia.
    - split; [lia|]. split; [lia|]. split; [| lia]. clear - S3'. exact S3'.
    - exact E13.
    - lia.
    - lia.
    - lia.
    - lia.
    - apply (writableZ_sok M (U sp - 464) (U sp)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - change (1064728 + 32) with 0x103f38. exact KC_sbeg.
    - apply (repx_rd (XL c) M M0 D (RIz + 32) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G32].
    - apply (repx_rd (XL c) M M0 D (RIz + 48) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G48].
    - apply (repx_rd (XL c) M M0 D (RIz + 56) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G56].
    - apply (repx_rd (XL c) M M0 D (RIz + 16) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G16].
    - change (1064728 + 40) with 0x103f40. exact KC_rel.
    - change (1064728 + 56) with 0x103f50. rewrite <- (w2b1 0) by lia. exact KC_pre.
    - exact KC_pg.
    - exact KC_P.
    - exact KC_gcf.
    - change (1675432 + 260) with 0x1991ac. rewrite <- (w2b1 0) by lia. exact KC_dpm.
    - change (1675432 + 144) with 0x199138. exact KC_lim.
    - left. rewrite <- ELO. lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply lazy_cover_HID.
    - (* [comment removed for export] *)
      intros mdlm r1 SBm MIm HLm G10' G11' G12' G13' G14' G15' Qok' Qf' K1.
      destruct (NODEF mdlm SBm MIm) as (N1 & N2 & N3 & N4 & N5 & _).
      apply (node1_of_fixedin3_s r1 _ rom mdlm addr size Qok' Qf' HLm); [ | exact G11' | exact G12' | exact G13' | exact G14' | exact G15' | | | | | exact N1 | exact N2 | exact N3 | exact N4 | exact N5 | ].
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite ELO. exact G10'.
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. exact SL4k.
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. reflexivity.
      + (lazymatch goal with |- ?G => let G' := eval unfold addr, size in G in change_no_check G' end). rewrite ELO. exact K1.
    - (* [comment removed for export] *)
      intros mdlm SBm MIm. destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & _ & HOK & MOKI & LZOK & HDS & MDSI & LZDS).
      split; [| split].
      + split; [exact HOK|]. split; [| exact MOKI]. exact (lazy_cover_sub Hd _ _ _ (lazy_cover_HID st mdl) LZOK).
      + split; [exact (halted_sbm mdl mdlm SBm HALT)|]. split; [| exact MIm].
        pose proof (same_but_materialized_frame mdl mdlm SBm) as (_ & _ & EL & _). rewrite EL. apply lazy_cover_HID.
      + split; [exact HDS|]. split; [| exact MDSI]. exact (lazy_cover_sub Hd _ _ _ (lazy_cover_HID st mdl) LZDS).
    - (* [comment removed for export] *)
      intros mdlm mdl4 SBm MIm SB4 MI4. split; [| exact (BUD mdlm mdl4 SBm SB4 MI4)].
      destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & _ & _ & _ & LZOK & _).
      pose proof (same_but_materialized_frame _ _ SB4) as (_ & _ & EL & _). rewrite EL.
      exact (lazy_cover_sub Hd2 _ _ _ (lazy_cover_mkH (m_vm_lazy mdl) A2 (m_vm_lazy mdl) (incl_refl _)) LZOK).
    - destruct (pos_mod4096 T T1 T4k) as [T4 T8]. split; [exact UT|]. split; [exact T4|]. split; [lia | exact T8].
    - clear - TSP ERI E9 E10. lia.
    - rewrite <- ESH. clear - TBAND SHB0 SHB1. lia.
    - rewrite <- ESH. right. lia.
    - rewrite <- ELO. clear - TSP SL0 SL1. lia.
    - rewrite <- ELO. right. lia.
    - rewrite <- ELO.
      apply (pk_poisonH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl RP D YIMG lo (Z_to_bv 64 331536) (at_ sp (-64)));
        [(lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia | lia | exact SL8 | rewrite at_u by lia; lia | rewrite at_u by lia; lia | | apply ret_ok_lit; [lia | reflexivity]].
      intros i Hi. rewrite at_u in Hi by lia. apply WSTK. lia.
    - apply (pk_gctH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl W RP D YIMG YCTX (at_ (at_ sp (-64)) (-16)) tp Etp);
        [rewrite !at_u by (rewrite ?at_u by lia; lia); lia | rewrite !at_u by (rewrite ?at_u by lia; lia); lia |].
      intros i Hi. rewrite !at_u in Hi by (rewrite ?at_u by lia; lia). apply WSTK. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. rewrite <- ELO.
      split; [left; lia|]. split; [left; lia|]. split; [left; lia|]. clear - CSP SL0 SL1. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite Etp. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. clear - CBAND SHB0 SHB1. lia.
    - replace (at_ thr 2872) with (Z_to_bv 64 (T + 2872)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R72.
    - replace (at_ thr 2880) with (Z_to_bv 64 (T + 2880)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R80.
    - replace (at_ thr 2792) with (Z_to_bv 64 (T + 2792)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact Rst.
    - apply (writableZ_sok M T (T + 4096)); [exact TWR | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (writableZ_sok M RIz (RIz + 128)); [apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW] | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells, asan_poison_tab in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm] in G in change_no_check G' end).
      repeat (constructor; [apply HOFF; intros z Hz; apply NH2s; lia|]). constructor.
    - rewrite <- ESH. apply HOFF. exact NH2sh.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite Etp. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2rt. right. lia.
    - apply HOFF. intros z Hz. apply NH2rt. left. lia.
    - apply HOFF. exact NH2ri.
    - apply HOFF. intros z Hz. apply NH2s; lia.
    - apply HOFF. exact NHri.
    - (* [comment removed for export] *)
      intros r' mdlm mdl5 SBm MIm SB5 MI5 PR Q1 Q10 Q11 Q12 Q13 Q9 Q19 Q20 Q4 Q3.
      rewrite <- ELO.
      destruct (LEDOK mdlm mdl5 SBm SB5) as (LED & SEV & LK & MW5 & HL5).
      set (MR := pf_mr M sp ra s0v s1v s2v s3v s4v s5v s6v (at_ thr 2768) RIz SBEG c mu PGP).
      set (M' := pam_3 MR sp thr v72 v80 vst RIz SBEG c lo mu).
      assert (ESH2 : SH = lo / 8 + 2147450880) by (rewrite ESH'; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); lia).
      assert (OUTM : forall a : word, (U a < U sp - 464 \/ U sp <= U a) -> (U a < lo \/ lo + 2 ^ 18 <= U a) -> (U a < SH \/ SH + 2 ^ 15 <= U a) ->
                 (U a < T + 2792 \/ T + 2800 <= U a) -> (U a < T + 2872 \/ T + 2888 <= U a) -> (U a < RIz + 48 \/ RIz + 56 <= U a) -> M' a = M a).
      { intros a X1 X2 X3 X4 X5 X6. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end).
        rewrite (pam_3_outside MR sp thr v72 v80 vst RIz SBEG c lo mu ltac:(lia) ltac:(lia) a
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - X1; lia)
                   ltac:(rewrite <- ESH2; exact X3) ltac:(rewrite UT; exact X4) ltac:(rewrite UT; exact X5) X6).
        (lazymatch goal with |- ?G => let G' := eval unfold MR in G in change_no_check G' end). apply pf_mr_outside; [lia | rewrite <- ELO; lia | exact X1 | rewrite <- ELO; exact X2]. }
      assert (GRM : mem_grows M M').
      { (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). eapply mem_grows_trans; [| apply pam_3_grows]. (lazymatch goal with |- ?G => let G' := eval unfold MR in G in change_no_check G' end). apply pf_mr_grows. }
      assert (DEFSL : forall a : word, lo <= U a < lo + 2 ^ 18 -> M' a <> None).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply pam_3_grows. (lazymatch goal with |- ?G => let G' := eval unfold MR, pf_mr in G in change_no_check G' end). apply wbytes_grows. (lazymatch goal with |- ?G => let G' := eval unfold zfill, zmem in G in change_no_check G' end). rewrite <- ELO. rewrite !u_Z2bv by lia.
        rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. discriminate. }
      assert (WRIM : writableZ ASEGS M RIz (RIz + 128)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW]).
      assert (FOOTM : forall a : word, M' a <> M a ->
                ((U sp - 464 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ (SH <= U a < SH + 2 ^ 15)
                 \/ (T + 2792 <= U a < T + 2800) \/ (T + 2872 <= U a < T + 2888) \/ (RIz + 48 <= U a < RIz + 56)) /\ M' a <> None).
      { intros a Ha.
        assert (IN : ((U sp - 464 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ (SH <= U a < SH + 2 ^ 15)
                      \/ (T + 2792 <= U a < T + 2800) \/ (T + 2872 <= U a < T + 2888) \/ (RIz + 48 <= U a < RIz + 56))
                     \/ ((U a < U sp - 464 \/ U sp <= U a) /\ (U a < lo \/ lo + 2 ^ 18 <= U a) /\ (U a < SH \/ SH + 2 ^ 15 <= U a)
                         /\ (U a < T + 2792 \/ T + 2800 <= U a) /\ (U a < T + 2872 \/ T + 2888 <= U a) /\ (U a < RIz + 48 \/ RIz + 56 <= U a))) by (clear; lia).
        destruct IN as [IN | (O1 & O2 & O3 & O4 & O5 & O6)]; [| exfalso; exact (Ha (OUTM a O1 O2 O3 O4 O5 O6))].
        split; [exact IN|].
        destruct IN as [I1 | [I2 | [I3 | [I4 | [I5 | I6]]]]].
        - apply GRM. destruct (WSTK (U a) I1) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        - exact (DEFSL a I2).
        - apply GRM. rewrite <- (Z_to_bv_bv_unsigned _ a). apply (pk_shadow_def bt (XL c) st Lc FF M M0 mdl RP D). (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). right. clear - I3 SHB0 SHB1. lia.
        - apply GRM. destruct (TWR (U a) ltac:(clear - I4; lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        - apply GRM. destruct (TWR (U a) ltac:(clear - I5; lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        - apply GRM. destruct (WRIM (U a) ltac:(clear - I6; lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      assert (W' : WF bt (add_meter (op_usermap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF).
      { apply (WF_meter bt (op_usermap st c) Lc FF 0 [(SH, SH + 2 ^ 18 / 8)] 0 (OPS_WF_usermap_pf bt st Lc FF c W Hc ROOM TIGHT MUR)); lia. }
      assert (RX' : RepX bt (XL c) (add_meter (op_usermap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF M' mdl5).
      { apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => XL c z /\ ~ False) (XL c)); [intros z [Hz _]; exact Hz|].
        apply (repx_step bt (XL c) (fun _ => False)
                 (fun z => (U sp - 464 <= z < U sp) \/ (lo <= z < lo + 2 ^ 18) \/ (SH <= z < SH + 2 ^ 15)
                           \/ (T + 2792 <= z < T + 2800) \/ (T + 2872 <= z < T + 2888) \/ (RIz + 48 <= z < RIz + 56))
                 Xdec_false st _ Lc Lc FF FF M M' mdl mdl5 RX FOOTM ltac:(intros a F; destruct F)).
        intros N0 N0' RPn Dn DIFF _ SAME.
        assert (EQF : forall a : word, ~ XL c (U a) -> N0' a = M' a) by (intros a Ha; apply SAME; exact (repx_off (XL c) M N0 Dn a Ha)).
        pose proof RPn as (_ & _ & _ & R4n & _). destruct (R4n c Hc) as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & GWn) _]. rewrite BT_segs in GWn. fold RIz in GWn.
        destruct LED as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13).
        apply (OPS_REP_usermap_pf bt st Lc FF N0 N0' mdl mdl5 c W RPn Hc ROOM); rewrite ?BT_segs.
        - intros a Ha. destruct (DIFF a Ha) as [[F | []] Dd]. split; [|exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold foot_usermap, uslot in G in change_no_check G' end). fold r; fold mu; fold rbeg; fold lo; fold RIz; fold SH. (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP, T_UNW in G in change_no_check G' end).
          replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. clear - F SP1 CR. lia.
        - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). fold r mu RIz. rewrite (rdn_ext ASEGS 8 N0' M' (Z_to_bv 64 (RIz + 48))); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | ].
          + (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). exact (pam_3_mu ASEGS MR sp thr v72 v80 vst RIz SBEG c lo mu ltac:(lia)).
          + intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply EQF. apply XRI. lia.
        - fold RIz. apply (repx_wr (fun _ => True) N0' N0 (fun a Ha => conj I (proj2 (DIFF a Ha)))); [lia | lia | exact GWn].
        - fold r; fold mu; fold rbeg; fold lo. (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). apply writableZ_of_def; [lia | lia |]. intros i Hi.
          rewrite (EQF (Z_to_bv 64 i)) by (rewrite u_Z2bv by lia; apply XSL; exact Hi). apply DEFSL. rewrite u_Z2bv by lia. exact Hi.
        - fold r; fold mu; fold rbeg; fold lo; fold SH. (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP, fillZ, byteZ, cellN in G in change_no_check G' end). replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. intros i Hi.
          rewrite w2b1 by ((lazymatch goal with |- ?G => let G' := eval unfold FA in G in change_no_check G' end); lia).
          rewrite (rdn_ext ASEGS 1 N0' M' (Z_to_bv 64 i)); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; rewrite u_Z2bv in Hx by lia; cbn in Hx; apply EQF, XSH; lia].
          replace i with (lo / 8 + 2147450880 + (i - SH)) by lia.
          exact (pam_3_fill ASEGS MR sp thr v72 v80 RIz lo ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite <- ESH2; right; lia)
                   ltac:(rewrite <- ESH2, UT; clear - TBAND SHB0 SHB1; lia) ltac:(rewrite <- ESH2; right; lia) vst SBEG c mu (i - SH) ltac:(lia)).
        - exact L1. - exact L2. - exact L3. - exact L4. - exact L5. - exact L6. - exact L7. - exact L8. - exact L9. - exact L10. - exact L11. - exact L12.
        - exact MI5.
        - exact L13. }
      apply (CONT1 r' M' mdl5 W' RX' SEV LK MW5 HL5); [ | | exact PR | exact Q1 | exact Q10 | exact Q11 | exact Q12 | exact Q13 | exact Q9 | exact Q19 | exact Q20 | exact Q4 | exact Q3].
      + intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [| exact Dd]. replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. fold RIz. clear - F. lia.
      + intros k v Hin.
        assert (K : -64 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        rewrite (rdn_ext ASEGS 8 M' MR (at_ sp k)); [ | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | ].
        * (lazymatch goal with |- ?G => let G' := eval unfold MR in G in change_no_check G' end). apply pf_mr_slots; [lia | rewrite <- ELO; lia | rewrite <- ELO; left; lia | exact Hin].
        * intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end).
          apply (pam_3_outside MR sp thr v72 v80 vst RIz SBEG c lo mu ltac:(lia) ltac:(lia) x ltac:(lia) ltac:(lia) ltac:(lia));
            [right; lia | rewrite <- ESH2; right; lia | rewrite UT; right; lia | rewrite UT; right; lia | right; lia].
    - (* [comment removed for export] *)
      intros r0 r' mdlm mdl5 SBm MIm SB5 MI5 AG POST. cbv beta in SB5.
      match goal with |- katD _ (mkCfg (mkst _ _ ?MKK _) _) _ => set (MK := MKK) end.
      pose proof (same_but_materialized_trans _ _ _ SBm SB5) as SBK.
      assert (OUTK : forall a : word, (U a < U sp - 464 \/ U sp <= U a) -> MK a = M a).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite mfi_m1_outside by (rewrite ?at_u by lia; lia). apply pf_m0_outside; lia. }
      assert (GRK : mem_grows M MK).
      { (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end). do 2 (eapply mem_grows_trans; [| apply wbytes_grows]). eapply mem_grows_trans; [apply pf_m0_grows | apply mfi_m1_grows]. }
      assert (FOOTK : forall a : word, MK a <> M a -> (U sp - 464 <= U a < U sp) /\ MK a <> None).
      { intros a Ha. assert (IN : (U sp - 464 <= U a < U sp) \/ (U a < U sp - 464 \/ U sp <= U a)) by (clear; lia).
        destruct IN as [IN | O1]; [| exfalso; exact (Ha (OUTK a O1))]. split; [exact IN|].
        apply GRK. destruct (WSTK (U a) IN) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      apply (CONT0 r0 r' MK mdl5 st (or_introl eq_refl) W); [ | exact (same_but_materialized_except_vm _ _ SBK) | exact (lazy_kept_sbm bt Lc FF mdl mdl5 SBK)
                                                              | exact (model_ivs_wf_sbm mdl mdl5 SBK MW) | exact (halted_sbm mdl mdl5 SBK HALT) | | exact AG | exact POST].
      + apply (repx_frame_step bt (XL c) st Lc FF M MK mdl mdl5 W RX); [| exact MI5 | exact SBK].
        intros a Ha. destruct (FOOTK a Ha) as [IN Dd]. split; [|exact Dd].
        intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa). lia.
      + intros a Ha. left. exact (FOOTK a Ha).
    - (* [comment removed for export] *)
      intros r0 r' mdlm mdl5 SBm MIm SB5 MI5 AG POST. rewrite <- ELO.
      match goal with |- katD _ (mkCfg (mkst _ _ ?MKK _) _) _ => set (MD := MKK) end.
      destruct (LEDDS mdlm mdl5 SBm SB5) as (LD & EAG & SEV & LK & MW5 & HL5).
      assert (OUTD : forall a : word, (U a < U sp - 464 \/ U sp <= U a) -> (U a < lo \/ lo + 2 ^ 18 <= U a) -> MD a = M a).
      { intros a Ha Hb. (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite unfill_out by (rewrite !u_Z2bv by lia; exact Hb).
        rewrite mfi_m1_outside by (rewrite ?at_u by lia; lia). apply pf_m0_outside; lia. }
      assert (SLD : forall a : word, lo <= U a < lo + 2 ^ 18 -> MD a = None).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        (lazymatch goal with |- ?G => let G' := eval unfold unfill in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
      assert (STD : forall a : word, U sp - 464 <= U a < U sp -> MD a <> None).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end).
        set (MU := unfill (Z_to_bv 64 lo) (Z_to_bv 64 (2 ^ 18)) _) in *.
        assert (GU : forall x : word, U sp - 464 <= U x < U sp -> MU x <> None).
        { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MU in G in change_no_check G' end). rewrite unfill_out by (rewrite !u_Z2bv by lia; lia).
          apply mfi_m1_grows. apply pf_m0_grows. destruct (WSTK (U x) Hx) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
        do 2 apply wbytes_grows. exact (GU a Ha). }
      assert (FOOTD : forall a : word, MD a <> M a -> ((U sp - 464 <= U a < U sp) /\ MD a <> None) \/ (lo <= U a < lo + 2 ^ 18)).
      { intros a Ha. assert (IN : (U sp - 464 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ ((U a < U sp - 464 \/ U sp <= U a) /\ (U a < lo \/ lo + 2 ^ 18 <= U a))) by (clear; lia).
        destruct IN as [IN | [IN | [O1 O2]]]; [left; split; [exact IN | exact (STD a IN)] | right; exact IN | exfalso; exact (Ha (OUTD a O1 O2))]. }
      assert (W1 : WF bt (op_uhole st c) Lc FF) by (apply (WF_uhole bt st Lc FF c Hc W)).
      apply (CONT0 r0 r' MD mdl5 (op_uhole st c) (or_intror eq_refl) W1); [ | exact SEV | exact LK | exact MW5 | exact HL5 | | exact AG | exact POST].
      + set (N1 := unfill (Z_to_bv 64 lo) (Z_to_bv 64 (2 ^ 18)) M0).
        assert (RP1 : Rep bt (op_uhole st c) Lc FF N1 mdl5).
        { apply (OPS_REP_uhole_pf bt st Lc FF M0 N1 mdl mdl5 c W RP Hc UH ltac:(fold r mu; (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP, KREGION_EXHAUST in G in change_no_check G' end); lia)); [ | exact LD | exact MI5 | exact EAG].
          intros a Ha. unfold N1, unfill in Ha |- *. rewrite !u_Z2bv in Ha |- * by lia. (lazymatch goal with |- ?G => let G' := eval unfold uslot in G in change_no_check G' end). fold r; fold mu; fold rbeg; fold lo. (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end).
          destruct (Z.leb_spec lo (U a)); destruct (Z.ltb_spec (U a) (lo + 2 ^ 18)); cbn [andb] in Ha |- *; first [split; [lia | reflexivity] | exfalso; exact (Ha eq_refl)]. }
        set (N := fun a : word => if Z_le_dec lo (U a) then (if Z_lt_dec (U a) (lo + 2 ^ 18) then None else if decide (M a = M0 a) then MD a else M0 a)
                                  else if decide (M a = M0 a) then MD a else M0 a).
        assert (N1in : forall a : word, lo <= U a < lo + 2 ^ 18 -> N1 a = None).
        { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold N1, unfill in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
        assert (N1out : forall a : word, (U a < lo \/ lo + 2 ^ 18 <= U a) -> N1 a = M0 a).
        { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold N1 in G in change_no_check G' end). apply unfill_out. rewrite !u_Z2bv by lia. exact Ha. }
        exists N. split.
        * apply (Rep_frame bt (op_uhole st c) Lc FF N1 N mdl5 W1 RP1). intros a Ha. unfold N in Ha |- *.
          destruct (Z_le_dec lo (U a)) as [L1'|L1']; [destruct (Z_lt_dec (U a) (lo + 2 ^ 18)) as [L2'|L2']|].
          -- exfalso. apply Ha. symmetry. apply N1in. lia.
          -- rewrite (N1out a ltac:(lia)) in Ha. destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
             rewrite <- E in Ha. destruct (FOOTD a Ha) as [[IN Dd] | IN]; [| lia]. split; [|exact Dd].
             intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia (op_uhole st c) Lc FF (U a) W1 RCa). lia.
          -- rewrite (N1out a ltac:(lia)) in Ha. destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
             rewrite <- E in Ha. destruct (FOOTD a Ha) as [[IN Dd] | IN]; [| lia]. split; [|exact Dd].
             intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia (op_uhole st c) Lc FF (U a) W1 RCa). lia.
        * intros a Ha. unfold N in Ha.
          assert (CASE : forall (E : M a <> M0 a), XL c (U a) /\ MD a <> None).
          { intros NE. destruct (D a NE) as [HX Dd]. split; [exact HX|].
            destruct (decide (MD a = M a)) as [EQ2 | NE2]; [rewrite EQ2; exact Dd|].
            destruct (FOOTD a NE2) as [[_ Dd2] | IN]; [exact Dd2 | exfalso; exact (XSL (U a) IN HX)]. }
          destruct (Z_le_dec lo (U a)) as [L1'|L1']; [destruct (Z_lt_dec (U a) (lo + 2 ^ 18)) as [L2'|L2']|].
          -- exfalso. apply Ha. apply SLD. lia.
          -- destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl) | exact (CASE NE)].
          -- destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl) | exact (CASE NE)].
      + intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end). exact (FOOTD a Ha).
  Qed.

End L3.
End WithCeil.
