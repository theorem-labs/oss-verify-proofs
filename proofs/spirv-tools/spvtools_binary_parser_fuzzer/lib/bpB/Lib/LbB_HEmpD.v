(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_HEmpS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_END : Z := 0xfa8f0.
Definition E_EPI : Z := 0xfa908.
Definition E_RET : Z := 0xfa93c.

Definition shEe (e : expr) : expr := EAlu ALU_ADD (EAlu ALU_SRL e (ELit 3)) (ELit 2147450880).
Definition rShe (w : word) : word := alu64 ALU_ADD (alu64 ALU_SRL w (Z_to_bv 64 3)) (Z_to_bv 64 2147450880).

Lemma wr_at_subE : forall m a n a' n', wr_at asegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W0 & W1 & W) H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
Qed.

Section EmpC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc key : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).

  Definition QF : config -> Prop :=
    emp_post H ra (Z_to_bv 64 spz) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0.

  Definition spf : Z := spz - 96.

  Definition FRAME (m : mem) : Prop :=
    rw_cells asegs m spf [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma stage_epi : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p v bl' bc' : Z) (ents' : list (Z * (Z * Z))) (inserted rehashed : bool),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) (Z_to_bv 64 (b2z inserted)) y12 y13 y14 y15 y16 y17
                             y18 y19 y20 y21 y22 y23 y24 y25 y26 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_EPI) fc None m (seg_rom asegs) ->
    frm_zero fc ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    FRAME m -> spz mod 16 = 0 -> 2 ^ 45 <= spf -> spz <= 2 ^ 47 -> bv_unsigned ra mod 2 = 0 ->
    mem_inv asegs m -> stk asegs m lo spz -> rw_cells asegs m (errno_addr tp) [C4 errv'] -> as_rauxv_ok H m B ->
    umapx MI_A 24 (nval24 ASEGS) (lbl LB') m obj bl' bc' ents' -> umap_sh m 24 (bl', bc', ents') ->
    addressable m obj 40 -> wr_at asegs m obj 40 ->
    In (p, (key, v)) ents' ->
    (inserted = false -> ents' = ents /\ rehashed = false) ->
    (inserted = true -> v = 0 /\ Permutation ents' ((p, (key, 0)) :: ents)) ->
    (rehashed = false -> bl' = bl /\ bc' = bc) ->
    (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc) ->
    as_RHEAP H s LB' m -> Permutation LB' (LB0 ++ LBm') -> Permutation (lbl LBm') (umap_blocks 24 bl' bc' ents') ->
    lb_own LBm' m ->
    xpres H LB0 spz [(obj, obj + 40)] m0 m ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 - (if rehashed then ICM (8 * bc') else 0) ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 errv'
      LB' LBm' p v bl' bc' ents' inserted rehashed
      at_epi fcsr_zero kernel_rel model_pres saved_regs sp_align sp_low sp_high ra_even
      minv stack_ok errno_cell auxv_ok map_rep map_shadow obj_addr obj_wr entry_in
      when_found when_new when_kept when_grown heap_rep heap_split blocks_perm owned outside_pres frames_rep consts
      stack_shadow alloc_budget.
    remember (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) (Z_to_bv 64 (b2z inserted)) y12 y13 y14
                  y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 s11 y28 y29 y30 y31) as regs0 eqn:regs0_is.
    pose (E := Eseed regs0 [ra; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; Z_to_bv 64 spf]).
    assert (seeded : regs_ok E (srs sr_id [(2%bv, EVar 44)]) regs0).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      apply Forall_cons; [|apply Forall_nil]. split; [intros sp_zero; discriminate sp_zero|].
      subst regs0 E; evs; reflexivity. }
    assert (full0 : rfull regs0) by (rewrite regs0_is; apply rfull_mkR).
    assert (sp_val : ev E 44 = Z_to_bv 64 spf) by reflexivity.
    assert (slot : forall (off : Z) (x : word) (n : N), 0 <= off <= 88 ->
              cell_at [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] (Z.to_nat off) = Some (C8 x) ->
              ev E n = x -> kentry_ok asegs E m (KWord (SA (EVar 44) off) 8 (EVar n))).
    { intros off x n off_range at_off val_n.
      unfold spf in sp_low.
      eapply (kword_of_rw_cells asegs E m spf _ (Z.to_nat off) (C8 x)); [exact saved_regs | exact at_off | reflexivity | lia | | | |].
      - unfold estart. cbn [a_base a_off edenot]. rewrite sp_val, u64_of_Z by (unfold spf; lia). lia.
      - unfold spf; lia.
      - unfold spf; lia.
      - cbn [edenot]. rewrite val_n. reflexivity. }
    assert (restore_known : know_ok asegs E m
      [KWord (SA (EVar 44) 88) 8 (EVar 32); KWord (SA (EVar 44) 80) 8 (EVar 33); KWord (SA (EVar 44) 72) 8 (EVar 34);
       KWord (SA (EVar 44) 64) 8 (EVar 35); KWord (SA (EVar 44) 56) 8 (EVar 36); KWord (SA (EVar 44) 48) 8 (EVar 37);
       KWord (SA (EVar 44) 40) 8 (EVar 38); KWord (SA (EVar 44) 32) 8 (EVar 39); KWord (SA (EVar 44) 24) 8 (EVar 40);
       KWord (SA (EVar 44) 16) 8 (EVar 41); KWord (SA (EVar 44) 8) 8 (EVar 42); KWord (SA (EVar 44) 0) 8 (EVar 43)]).
    { unfold know_ok.
      repeat (apply Forall_cons; [eapply slot; [lia | reflexivity | reflexivity] |]).
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs regs0 E_EPI m (seg_rom asegs) seeded restore_known 40%nat [E_RET] (SCR [] [] []) 45%N.
    { unfold spf in sp_low. split_scs; cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
        rewrite sp_val, u64_of_Z by (unfold spf; lia); cbn [elenZ edenot]; unfold spf; rewrite ?u64_of_Z by lia; lia. }
    readback HR' (msteps_full asegs _ _ Hms full0) regs0_is regs_after.
    rreg HR' 1%bv got_ra. rreg HR' 2%bv got_sp. rreg HR' 8%bv got_s0. rreg HR' 9%bv got_s1.
    rreg HR' 18%bv got_s2. rreg HR' 19%bv got_s3. rreg HR' 20%bv got_s4. rreg HR' 21%bv got_s5. rreg HR' 22%bv got_s6.
    rreg HR' 23%bv got_s7. rreg HR' 24%bv got_s8. rreg HR' 25%bv got_s9. rreg HR' 26%bv got_s10.
    rewrite (w_add spf 96) in got_sp by (unfold spf in *; lia).
    replace (spf + 96) with spz in got_sp by (unfold spf; lia).
    rewrite got_ra, got_sp, got_s0, got_s1, got_s2, got_s3, got_s4, got_s5, got_s6, got_s7, got_s8, got_s9, got_s10 in regs_after.
    assert (ret_run : evt asegs (fun ms => ms = MS (mkR ra (Z_to_bv 64 spz) gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (b2z inserted))
                                                    y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                                                F (ret_pc ra) fc None m (seg_rom asegs))
                          (MS R' F (Z_to_bv 64 E_RET) fc None m (seg_rom asegs))).
    { rewrite regs_after. unfold E_RET. step. apply evt_done. reflexivity. }
    eapply (sr_evt H HH QF _ s msF mo regs0 F (Z_to_bv 64 E_EPI) fc m (seg_rom asegs) kernel_rel at_epi).
    { eapply evt_of_msteps; [exact Hms | exact ret_run]. }
    intros msF' mo' kernel_rel' model_step at_ret.
    unfold QF, emp_post.
    exists y5, y6, y7, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m, errv', s, LB', LBm', F, fc, p, v, bl', bc', ents',
      inserted, rehashed.
    rewrite u64_of_Z by (unfold spf in sp_low; lia).
    refine (conj at_ret (conj fcsr_zero (conj kernel_rel' (conj _ (conj minv (conj stack_ok (conj errno_cell (conj auxv_ok
             (conj map_rep (conj map_shadow (conj obj_addr (conj obj_wr (conj entry_in (conj when_found (conj when_new
             (conj when_kept (conj when_grown (conj heap_rep (conj heap_split (conj blocks_perm (conj owned (conj outside_pres
             (conj frames_rep (conj consts (conj stack_shadow alloc_budget))))))))))))))))))))))))).
    exact (ah_mpres_trans H HH _ _ _ model_pres model_step).
  Qed.

  Lemma obj_window_ok : forall LBx m a b, as_RFS H LF m -> map_live_frame LF obj -> obj <= a -> b <= obj + 40 ->
    aclient_write_ok H LBx (a, b) /\ afs_write_ok H LF (a, b) /\ aconst_ok (a, b) /\ stack0_ok (a, b).
  Proof.
    intros LBx m a b RF (fv & INV & FV1 & FV2) Ha Hb.
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK FR]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4).
    pose proof (FR fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
    pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
    assert (VA : aapp obj 40) by (eapply aapp_sub; [exact FS4 | unfold AFS_SIZE; lia | unfold AFS_SIZE; lia]).
    split; [right; right; right; right; left; cbn; unfold AFS_SIZE in *; lia|].
    split; [right; exists fv; split; [exact INV | cbn; lia]|].
    split; [eapply (aconst_ok_app obj 40); [exact VA | cbn; lia | cbn; lia]|].
    eapply (stack0_ok_aapp obj 40); [exact VA | cbn; lia | cbn; lia].
  Qed.

  Lemma obj_place : forall m, as_RFS H LF m -> map_live_frame LF obj ->
    aapp obj 40 /\ as_FSB H <= obj /\ obj + 40 <= as_FSB H + AFS_SIZE /\ AIMG_TOP <= obj.
  Proof.
    intros m RF (fv & INV & FV1 & FV2).
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK FR]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4).
    pose proof (FR fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
    pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
    split; [eapply aapp_sub; [exact FS4 | unfold AFS_SIZE; lia | unfold AFS_SIZE; lia]|].
    unfold AFS_SIZE, AIMG_TOP in *. split; [lia|]. split; [lia|]. lia.
  Qed.

  Lemma stage_found : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p v : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                             y18 y19 y20 y21 y22 y23 y24 y25 y26 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_FOUND) fc None m (seg_rom asegs) ->
    frm_zero fc ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    FRAME m -> spz mod 16 = 0 -> 2 ^ 45 <= spf -> spz <= 2 ^ 47 -> bv_unsigned ra mod 2 = 0 ->
    mem_inv asegs m -> stk asegs m lo spz -> rw_cells asegs m (errno_addr tp) [C4 errv'] -> as_rauxv_ok H m B ->
    umapx MI_A 24 (nval24 ASEGS) (lbl LB') m obj bl bc ents -> umap_sh m 24 (bl, bc, ents) ->
    addressable m obj 40 -> wr_at asegs m obj 40 ->
    In (p, (key, v)) ents ->
    as_RHEAP H s LB' m -> Permutation LB' (LB0 ++ LBm') -> Permutation (lbl LBm') (umap_blocks 24 bl bc ents) ->
    lb_own LBm' m ->
    xpres H LB0 spz [(obj, obj + 40)] m0 m ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 errv'
      LB' LBm' p v at_found fcsr_zero kernel_rel model_pres saved_regs sp_align sp_low sp_high ra_even
      minv stack_ok errno_cell auxv_ok map_rep map_shadow obj_addr obj_wr entry_in
      heap_rep heap_split blocks_perm owned outside_pres frames_rep consts stack_shadow alloc_budget.
    remember (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) y11 y12 y13 y14
                  y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 s11 y28 y29 y30 y31) as regs0 eqn:regs0_is.
    assert (full0 : rfull regs0) by (rewrite regs0_is; apply rfull_mkR).
    pose (E := Eseed regs0 []).
    assert (seeded : regs_ok E sr_id regs0) by apply regs_ok_seed.
    assert (nothing_known : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs regs0 E_FOUND m (seg_rom asegs) seeded nothing_known 8%nat [E_EPI] (SCR [] [] []) 32%N.
    { split_scs. }
    readback HR' (msteps_full asegs _ _ Hms full0) regs0_is regs_after.
    rreg HR' 11%bv got_flag.
    rewrite got_flag in regs_after.
    change (Z_to_bv 64 0) with (Z_to_bv 64 (b2z false)) in regs_after.
    eapply (sr_blk_eq H HH); [exact kernel_rel | exact at_found | exact full0 | exact Hms | exact regs_after |].
    intros msF' mo' kernel_rel' model_step at_epi.
    eapply (stage_epi s msF' mo' m F fc y1 y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26
              y28 y29 y30 y31 errv' LB' LBm' p v bl bc ents false false at_epi fcsr_zero kernel_rel'
              (ah_mpres_trans H HH _ _ _ model_pres model_step) saved_regs sp_align sp_low sp_high ra_even
              minv stack_ok errno_cell auxv_ok map_rep map_shadow obj_addr obj_wr entry_in);
      try (intros flag_is; discriminate flag_is); try (intros; split; reflexivity);
      try eassumption.
    lia.
  Qed.

  Lemma stage_end : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl' bc' : Z) (ents' : list (Z * (Z * Z))) (rehashed : bool),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 (obj + 24)) y19 y20 y21 y22 y23 y24 y25 (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_END) fc None m (seg_rom asegs) ->
    frm_zero fc ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    FRAME m -> spz mod 16 = 0 -> 2 ^ 45 <= spf -> spz <= 2 ^ 47 -> bv_unsigned ra mod 2 = 0 ->
    mem_inv asegs m -> stk asegs m lo spz -> rw_cells asegs m (errno_addr tp) [C4 errv'] -> as_rauxv_ok H m B ->
    tp = Z_to_bv 64 ATP -> aceil <= spf ->
    map_live_frame LF obj -> obj mod 8 = 0 ->
    rw_cells asegs m (obj + 24) [C8 (Z_to_bv 64 (Zlength ents))] -> 0 <= Zlength ents < 2 ^ 60 ->
    (forall M', munch [(obj + 24, obj + 32)] m M' -> wmono asegs m M' -> rw_cells asegs M' (obj + 24) [C8 (Z_to_bv 64 (Zlength ents + 1))] ->
        umapx MI_A 24 (nval24 ASEGS) (lbl LB') M' obj bl' bc' ents') ->
    umap_sh m 24 (bl', bc', ents') ->
    (bc' <> 0 -> 0 <= bl' /\ bl' + 8 * bc' <= 2 ^ 47) -> (forall p k v, In (p, (k, v)) ents' -> 0 <= p /\ p + 24 <= 2 ^ 47) ->
    addressable m obj 40 -> wr_at asegs m obj 40 ->
    In (p, (key, 0)) ents' -> Permutation ents' ((p, (key, 0)) :: ents) ->
    (rehashed = false -> bl' = bl /\ bc' = bc) ->
    (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc) ->
    as_RHEAP H s LB' m -> Permutation LB' (LB0 ++ LBm') -> Permutation (lbl LBm') (umap_blocks 24 bl' bc' ents') ->
    lb_own LBm' m ->
    xpres H LB0 spz [(obj, obj + 40)] m0 m ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 - (if rehashed then ICM (8 * bc') else 0) ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 errv'
      LB' LBm' p bl' bc' ents' rehashed
      at_end fcsr_zero kernel_rel model_pres saved_regs sp_align sp_low sp_high ra_even
      minv stack_ok errno_cell auxv_ok tp_is ceil_below obj_live obj_align size_cell size_range map_after
      map_shadow table_range node_range obj_addr obj_wr entry_in entries_perm when_kept when_grown
      heap_rep heap_split blocks_perm owned outside_pres frames_rep consts stack_shadow alloc_budget.
    destruct (obj_place m frames_rep obj_live) as (obj_app & _ & _ & img_below).
    destruct (obj_window_ok LB' m (obj + 24) (obj + 32) frames_rep obj_live ltac:(lia) ltac:(lia))
      as (win_client & win_frames & win_const & win_stack0).
    pose proof aceil_facts as ceil_range.
    assert (obj_top : obj + 40 <= aceil).
    { unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO in obj_app. lia. }
    unfold spf in sp_low, ceil_below. unfold AIMG_TOP in img_below.
    assert (field_wr : wr_at asegs m (obj + 24) 8) by (apply (wr_at_subE m obj 40); [exact obj_wr | lia | lia | lia]).
    assert (field_cell : cellw asegs m (obj + 24) 8 (Zlength ents)) by (apply cellw8_of_rw_cells; [exact size_cell | lia ..]).
    assert (field_sh0 : sh0 m (obj + 24)).
    { eapply sh0_of_addressable; [exact obj_addr|]. change (8 * (40 / 8)) with 40. lia. }
    remember (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 (obj + 24)) y19 y20 y21 y22 y23 y24 y25 (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31)
      as regs0 eqn:regs0_is.
    assert (full0 : rfull regs0) by (rewrite regs0_is; apply rfull_mkR).
    pose (E := Eseed regs0 [Z_to_bv 64 (Zlength ents)]).
    assert (field_val : ev E 18 = Z_to_bv 64 (obj + 24)) by (subst E regs0; reflexivity).
    assert (size_val : ev E 32 = Z_to_bv 64 (Zlength ents)) by reflexivity.
    assert (seeded : regs_ok E (srs sr_id [(26%bv, shEe (EVar 18))]) regs0).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      apply Forall_cons; [|apply Forall_nil]. split; [intros s10_zero; discriminate s10_zero|].
      cbn [fst snd]. unfold shEe. cbn [edenot]. rewrite field_val, regs0_is. reflexivity. }
    assert (field_known : know_ok asegs E m
      [KWord (SA (EAlu ALU_SRL (EVar 18) (ELit 3)) SHBASE) 1 (ELit 0); KWr (SA (EVar 18) 0) (ELit 8)]).
    { unfold know_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - apply (kshadow0 E m (EVar 18) (obj + 24)); [exact field_val | lia | exact field_sh0].
      - apply (kwr_of_wr_at asegs E m (obj + 24) 8); [exact field_wr | | |];
          unfold estart, elenZ; cbn [a_base a_off edenot]; rewrite ?field_val, ?u64_of_Z by lia; lia. }
    xrun_at (PropExec.mkFP F fc) asegs regs0 E_END m (seg_rom asegs) seeded field_known 40%nat [E_EPI] (SCR [] [EVar 32] []) 33%N.
    { split_scs.
      - eapply (sc_read_cellw asegs E m (SA (EVar 18) 0) (obj + 24) 8 (Zlength ents) (EVar 32) field_cell); [lia | |exact size_val].
        unfold adenot. cbn [a_base a_off edenot]. rewrite field_val, v_addi_Z by lia. f_equal. lia.
      - cbn [sc_denot]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite field_val, !u64_of_Z by lia. lia.
      - cbn [sc_denot]. unfold flat, elenZ, estart. cbn [a_base a_off].
        rewrite (LbB_Kit.srl3_val E (EVar 18) (obj + 24) field_val) by lia.
        cbn [edenot]. rewrite u64_of_Z by lia.
        pose proof (div8_bound (obj + 24) ltac:(lia)). lia. }
    lazymatch type of Hms with CatSim.msteps _ _ (PropExec.mkst _ _ ?mem_end _) =>
      change mem_end with (mem_denot E m [SE (SA (EVar 18) 0) 8 (EAlu ALU_ADD (EVar 32) (ELit 1))]) in Hms end.
    set (M1 := mem_denot E m [SE (SA (EVar 18) 0) 8 (EAlu ALU_ADD (EVar 32) (ELit 1))]) in Hms.
    set (W := [(obj + 24, obj + 32)]).
    assert (grow_munch : munch W m M1).
    { subst M1 W. apply munch_mem_denot; [exact Hlf|]. apply Forall_cons; [|apply Forall_nil].
      cbn [e_addr e_width]. unfold estart. cbn [a_base a_off edenot]. rewrite field_val, u64_of_Z by lia. cbn [inside]. left. lia. }
    assert (grow_wmono : wmono asegs m M1) by apply wmono_mem_denot.
    assert (new_size : rw_cells asegs M1 (obj + 24) [C8 (Z_to_bv 64 (Zlength ents + 1))]).
    { apply (rw_cells_mem_denot_w E m [] (SA (EVar 18) 0) 8 (EAlu ALU_ADD (EVar 32) (ELit 1)) [] (obj + 24));
        [exact Hlf | apply Forall_nil | | exact field_wr | reflexivity | exact I |].
      - unfold estart. cbn [a_base a_off edenot]. rewrite field_val, u64_of_Z by lia. lia.
      - cbn [edenot]. rewrite size_val, w_add by lia. reflexivity. }
    pose proof (map_after M1 grow_munch grow_wmono new_size) as map_rep1.
    readback HR' (msteps_full asegs _ _ Hms full0) regs0_is regs_after.
    rreg HR' 11%bv got_flag.
    rewrite got_flag in regs_after.
    change (Z_to_bv 64 1) with (Z_to_bv 64 (b2z true)) in regs_after.
    eapply (sr_blk_eq H HH); [exact kernel_rel | exact at_end | exact full0 | exact Hms | exact regs_after |].
    intros msF' mo' kernel_rel' model_step at_epi.
    assert (shadow_clear : forall A n, 0 <= A -> 0 <= n -> A + n <= 2 ^ 47 -> disjoint_from W (sh A) (nsh n)).
    { intros A n A_lo n_lo A_hi. subst W. cbn [disjoint_from]. split; [|exact I].
      unfold aapp, aapp_lo, aapp_hi in obj_app. destruct obj_app as [[_ low_end] | [high_start _]].
      - right. unfold sh, ALOWSH_LO in *. rewrite ASHADOW_BASE_val. pose proof (Z.div_pos A 8 A_lo ltac:(lia)). lia.
      - left. pose proof (sh_nsh_high A n A_lo n_lo ltac:(unfold AAPP_HI; lia)). lia. }
    assert (frame1 : FRAME M1).
    { unfold FRAME in *. eapply rw_cells_transport; [exact saved_regs | exact grow_munch | exact grow_wmono |].
      subst W. cbn. split; [|exact I]. unfold spf. lia. }
    assert (errno1 : rw_cells asegs M1 (bv_unsigned tp + -164) [C4 errv']).
    { eapply rw_cells_transport; [exact errno_cell | exact grow_munch | exact grow_wmono |].
      subst W. rewrite tp_is, u64_of_Z by (unfold ATP; lia). cbn. split; [|exact I]. unfold ATP. lia. }
    destruct (client_frame H HH s LB' LF B W m M1 heap_rep frames_rep consts auxv_ok grow_munch grow_wmono
                (@Forall_cons _ _ _ _ win_client (Forall_nil _)) (@Forall_cons _ _ _ _ win_frames (Forall_nil _))
                (@Forall_cons _ _ _ _ win_const (Forall_nil _))) as (heap1 & frames1 & consts1 & auxv1).
    assert (stack01 : stack0 M1 lo shi)
      by exact (stack0_transport W m M1 lo shi stack_shadow grow_munch grow_wmono (@Forall_cons _ _ _ _ win_stack0 (Forall_nil _))).
    pose proof (LbB_HFind.BSEQ_boundA bc' (u_bseq map_rep1)) as bc_range.
    assert (sh1 : umap_sh M1 24 (bl', bc', ents')).
    { unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c in *. cbn [Datatypes.fst Datatypes.snd] in *.
      destruct map_shadow as [table_sh nodes_sh]. split.
      - intros bc_nz. destruct (table_range bc_nz) as [bl_lo bl_hi].
        eapply addressable_transport; [exact (table_sh bc_nz) | exact grow_munch | exact grow_wmono |].
        apply shadow_clear; lia.
      - intros q k val q_in. destruct (node_range q k val q_in) as [q_lo q_hi].
        eapply addressable_transport; [exact (nodes_sh q k val q_in) | exact grow_munch | exact grow_wmono |].
        apply shadow_clear; lia. }
    assert (addr1 : addressable M1 obj 40)
      by (eapply addressable_transport; [exact obj_addr | exact grow_munch | exact grow_wmono | apply shadow_clear; lia]).
    assert (xpres1 : xpres H LB0 spz [(obj, obj + 40)] m0 M1).
    { eapply (xpres_munch_mixed H HH s LB' LB0 LBm' spz [(obj, obj + 40)] W m0 m M1);
        [exact outside_pres | exact heap_rep | exact heap_split | lia | exact grow_munch | exact grow_wmono |].
      subst W. apply Forall_cons; [|apply Forall_nil]. right; left. intros a a_in. cbn in a_in |- *. left. lia. }
    assert (stk1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact stack_ok).
    exact (stage_epi s msF' mo' M1 F fc y1 y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) y19 y20 y21 y22 y23
             y24 y25 (getr R' 26) y28 y29 y30 y31 errv' LB' LBm' p 0 bl' bc' ents' true rehashed at_epi fcsr_zero kernel_rel'
             (ah_mpres_trans H HH _ _ _ model_pres model_step) frame1 sp_align sp_low sp_high ra_even
             (msteps_mem_inv asegs _ _ Hms minv) stk1 errno1 auxv1 map_rep1 sh1 addr1
             (wr_at_wmono m M1 obj 40 obj_wr grow_wmono) entry_in
             ltac:(intros flag_false; discriminate flag_false) (fun _ => conj eq_refl entries_perm) when_kept when_grown
             heap1 heap_split blocks_perm (lb_own_wmono LBm' m M1 owned grow_wmono) xpres1 frames1 consts1 stack01 alloc_budget).
  Qed.
End EmpC.
