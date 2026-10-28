(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
    intros s msF mo m F fc y1 y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31
      errv' LB' LBm' p v bl' bc' ents' inserted rehashed
      VIS FRZ KR MP FR SP16 SPL SPH RAE MI ST ERR RA U SH AD WR IN C1 C2 C3 C4 RH PE PM OWN XP RF AC S0 AL.
    unfold FRAME, spf in *.
    remember (mkR y1 (Z_to_bv 64 (spz - 96)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) (Z_to_bv 64 (b2z inserted)) y12 y13 y14 y15 y16 y17
                  y18 y19 y20 y21 y22 y23 y24 y25 y26 s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (spz - 96); s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KWord (SA (EVar 32) 16) 8 (EVar 35);
         KWord (SA (EVar 32) 24) 8 (EVar 36); KWord (SA (EVar 32) 32) 8 (EVar 37); KWord (SA (EVar 32) 40) 8 (EVar 38);
         KWord (SA (EVar 32) 48) 8 (EVar 39); KWord (SA (EVar 32) 56) 8 (EVar 40); KWord (SA (EVar 32) 64) 8 (EVar 41);
         KWord (SA (EVar 32) 72) 8 (EVar 42); KWord (SA (EVar 32) 80) 8 (EVar 43); KWord (SA (EVar 32) 88) 8 (EVar 44);
         KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 96) ]).
    { unfold know_ok.
      apply Forall_cons. { kword_cell FR 0%nat (C8 s10). }
      apply Forall_cons. { kword_cell FR 8%nat (C8 s9). }
      apply Forall_cons. { kword_cell FR 16%nat (C8 s8). }
      apply Forall_cons. { kword_cell FR 24%nat (C8 s7). }
      apply Forall_cons. { kword_cell FR 32%nat (C8 s6). }
      apply Forall_cons. { kword_cell FR 40%nat (C8 s5). }
      apply Forall_cons. { kword_cell FR 48%nat (C8 s4). }
      apply Forall_cons. { kword_cell FR 56%nat (C8 s3). }
      apply Forall_cons. { kword_cell FR 64%nat (C8 s2). }
      apply Forall_cons. { kword_cell FR 72%nat (C8 s1). }
      apply Forall_cons. { kword_cell FR 80%nat (C8 s0). }
      apply Forall_cons. { kword_cell FR 88%nat (C8 ra). }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R E_EPI m (seg_rom asegs) HR HK 40%nat [E_RET] (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1; try sc_shdj; try sc_dj. }
    clear HK.
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with m in Hms end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 18%bv G18.
    rreg HR' 19%bv G19. rreg HR' 20%bv G20. rreg HR' 21%bv G21. rreg HR' 22%bv G22. rreg HR' 23%bv G23.
    rreg HR' 24%bv G24. rreg HR' 25%bv G25. rreg HR' 26%bv G26.
    assert (G2' : getr R' 2 = Z_to_bv 64 spz) by (rewrite G2; rewrite ?w_addm, ?w_add, ?v_addi_Z by lia; try reflexivity; f_equal; lia).
    rewrite G1, G2', G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26 in HRe.
    eapply (sr_evt H HH) with
      (P := fun ms => exists u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6,
              ms = MS (mkR ra (Z_to_bv 64 spz) gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (b2z inserted)) b2 b3 b4 b5 b6 b7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (ret_pc ra) fc None m (seg_rom asegs));
      [exact KR | exact VIS | |].
    { eapply evt_of_msteps; [exact Hms|].
      rewrite mkst_MS, HRe. step. apply evt_done. do 13 eexists. reflexivity. }
    intros msF' mo' KR' MP' (u0 & u1 & u2 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & HP).
    unfold QF, emp_post.
    exists u0, u1, u2, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m, errv', s, LB', LBm', F, fc, p, v, bl', bc', ents', inserted, rehashed.
    rewrite u64_of_Z by lia.
    split; [exact HP|]. split; [exact FRZ|]. split; [exact KR'|]. split; [eapply (ah_mpres_trans H HH); [exact MP | exact MP']|].
    split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact RA|].
    split; [exact U|]. split; [exact SH|]. split; [exact AD|]. split; [exact WR|]. split; [exact IN|].
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
    split; [exact RH|]. split; [exact PE|]. split; [exact PM|]. split; [exact OWN|]. split; [exact XP|].
    split; [exact RF|]. split; [exact AC|]. split; [exact S0|]. exact AL.
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
    intros s msF mo m F fc y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31
      errv' LB' LBm' p v VIS FRZ KR MP FR SP16 SPL SPH RAE MI ST ERR RA U SH AD WR IN RH PE PM OWN XP RF AC S0 AL.
    unfold spf in *.
    remember (mkR y1 (Z_to_bv 64 (spz - 96)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                  y18 y19 y20 y21 y22 y23 y24 y25 y26 s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 p]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m []) by constructor.
    xrun_at (PropExec.mkFP F fc) asegs R E_FOUND m (seg_rom asegs) HR HK 10%nat [E_EPI] (SCR [] [] []) 50%N.
    { split_scs. }
    clear HK.
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with m in Hms end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms HF) HR0 HRe.
    rreg HR' 11%bv G11. rreg HR' 10%bv G10. rewrite G11, G10 in HRe.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact HF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (stage_epi s msF1 mo1 m F fc) with (inserted := false) (rehashed := false) (ents' := ents) (bl' := bl) (bc' := bc)
      (LB' := LB') (LBm' := LBm') (p := p) (v := v);
      [ unfold spf; exact VIS1 | exact FRZ | exact KR1 | eapply (ah_mpres_trans H HH); [exact MP | exact MP1] | unfold FRAME, spf; exact FR
      | exact SP16 | unfold spf; lia | exact SPH | exact RAE | exact MI | exact ST | exact ERR | exact RA | exact U | exact SH | exact AD | exact WR
      | exact IN | intros _; split; reflexivity | intros X; discriminate X | intros _; split; reflexivity | intros X; discriminate X
      | exact RH | exact PE | exact PM | exact OWN | exact XP | exact RF | exact AC | exact S0 | lia ].
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
    intros s msF mo m F fc y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31
      errv' LB' LBm' p bl' bc' ents' rehashed
      VIS FRZ KR MP FR SP16 SPL SPH RAE MI ST ERR RA TPV ACS LFO OAL CSZ SZR HU SH BLR NDR AD WR IN PERM CR3 CR4 RH PE PM OWN XP RF AC S0 AL.
    pose proof (obj_place m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK _]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4).
    assert (GZO : gz m obj 40) by (intros i Hi; eapply sh0_of_addressable; [exact AD | change (8 * (40 / 8)) with 40; lia]).
    unfold FRAME, spf in *.
    remember (mkR y1 (Z_to_bv 64 (spz - 96)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 (obj + 24)) y19 y20 y21 y22 y23 y24 y25 (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 p; Z_to_bv 64 (Zlength ents)]).
    assert (HR : regs_ok E (srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 24)); (26%bv, shEe (EAlu ALU_ADD (EVar 32) (ELit 24)));
                                        (10%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; unfold shEe, rShe; evs; rewrite ?w_add by lia; reflexivity] |]).
      apply Forall_nil. }
    assert (HK : know_ok asegs E m
       (kn_fix 20 [E_EPI] (SCR [] [] []) E_END (srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 24)); (26%bv, shEe (EAlu ALU_ADD (EVar 32) (ELit 24)));
                                                          (10%bv, EVar 33)])
         [ KWord (SA (EVar 32) 24) 8 (EVar 34); KWr (SA (EVar 32) 24) (ELit 8); KRange (EVar 32) 0x6e8000 (2 ^ 47 - 40);
           KRange (EVar 34) 0 (2 ^ 60) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CSZ 0%nat (C8 (Z_to_bv 64 (Zlength ents))). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact (wr_at_subE m obj 40 (obj + 24) 8 WR ltac:(lia) ltac:(lia) ltac:(lia)) | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
      do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_END m (seg_rom asegs) HR HK 40%nat [E_EPI] (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1; try sc_shdj; try sc_dj. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (MU1 : munch [(obj + 24, obj + 32)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (CSZ1 : rw_cells asegs M1 (obj + 24) [C8 (Z_to_bv 64 (Zlength ents + 1))]).
    { assert (EQv : map (fun v => C8 (edenot E v)) [EAlu ALU_ADD (EVar 34) (ELit 1)] = [C8 (Z_to_bv 64 (Zlength ents + 1))])
        by (cbn [map]; f_equal; f_equal; evs; rewrite w_add by lia; reflexivity).
      rewrite <- EQv. subst M1.
      change [{| e_addr := {| a_base := EVar 32; a_off := 24 |}; e_width := 8; e_val := EAlu ALU_ADD (EVar 34) (ELit 1) |}]
        with (c8log (EVar 32) 24 [EAlu ALU_ADD (EVar 34) (ELit 1)]) in Hlf |- *.
      apply rw_cells_c8log; [exact Hlf | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia |].
      cbn [length Z.of_nat]. exact (wr_at_subE m obj 40 (obj + 24) 8 WR ltac:(lia) ltac:(lia) ltac:(lia)). }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 11%bv G11. rreg HR' 10%bv G10. rewrite G11, G10 in HRe.

    destruct (obj_window_ok LB' m (obj + 24) (obj + 32) RF LFO ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4).
    destruct (client_frame H HH s LB' LF B [(obj + 24, obj + 32)] m M1 RH RF AC RA MU1 WM1
               (Forall_cons _ _ _ W1 (Forall_nil _)) (Forall_cons _ _ _ W2 (Forall_nil _)) (Forall_cons _ _ _ W3 (Forall_nil _)))
      as (RH1 & RF1 & AC1 & RA1).
    assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact (Forall_cons _ _ _ W4 (Forall_nil _))]).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv']).
    { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
      eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; unfold AFS_SIZE in *; lia]. }

    assert (OAPP : obj + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= obj).
    { unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA. lia. }
    assert (DSH : forall A n, 0 <= A -> 0 <= n -> A + n <= 2 ^ 47 -> disjoint_from [(obj + 24, obj + 32)] (sh A) (nsh n)).
    { intros A n HA Hn Han. cbn [disjoint_from]. split; [|exact I].
      pose proof (sh_nsh_high A n HA Hn ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN.
      assert (ASHADOW_BASE <= sh A) by (unfold sh; pose proof (Z.div_pos A 8 ltac:(lia) ltac:(lia)); lia). unfold ASHADOW_BASE in *. lia. }
    assert (FR1 : rw_cells asegs M1 (spz - 96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 |]. cbn [disjoint_from]. split; [|exact I].
      pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4). cbn [cells_size csize Z.of_nat]. unfold AFS_SIZE in *. lia. }
    assert (SH1 : umap_sh M1 24 (bl', bc', ents')).
    { destruct SH as [SHb SHn]. unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c in *. cbn [Datatypes.fst Datatypes.snd] in *.
      split.
      - intros Hbc. destruct (BLR Hbc) as [B0 B1]. pose proof (u_bseq (HU M1 MU1 WM1 CSZ1)) as BSQ.
        pose proof (LbB_HFind.BSEQ_boundA bc' BSQ) as BCR.
        eapply addressable_transport; [exact (SHb Hbc) | exact MU1 | exact WM1 | apply DSH; lia].
      - intros q k v Hin. destruct (NDR q k v Hin) as [P0 P1].
        eapply addressable_transport; [exact (SHn q k v Hin) | exact MU1 | exact WM1 | apply DSH; lia]. }
    assert (AD1 : addressable M1 obj 40) by (eapply addressable_transport; [exact AD | exact MU1 | exact WM1 | apply DSH; lia]).
    assert (XP1 : xpres H LB0 spz [(obj, obj + 40)] m0 M1).
    { eapply (xpres_trans H); [exact XP|].
      eapply (xpres_weaken H); [eapply (xpres_of_munch H s LB' spz [(obj, obj + 40)] [(obj + 24, obj + 32)] m m M1 HH RH MU1 WM1) | lia | |].
      - apply Forall_cons; [right; intros a Ha; cbn in Ha |- *; left; lia | apply Forall_nil].
      - intros b Hb. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. left. exact Hb.
      - intros a Ha. exact Ha. }
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (stage_epi s msF1 mo1 M1 F fc) with (inserted := true) (rehashed := rehashed) (ents' := ents') (bl' := bl') (bc' := bc')
      (LB' := LB') (LBm' := LBm') (p := p) (v := 0);
      [ unfold spf; exact VIS1 | exact FRZ | exact KR1 | eapply (ah_mpres_trans H HH); [exact MP | exact MP1] | unfold FRAME, spf; exact FR1
      | exact SP16 | unfold spf; lia | exact SPH | exact RAE | exact MI1 | exact ST1 | exact ERR1 | exact RA1 | exact (HU M1 MU1 WM1 CSZ1)
      | exact SH1 | exact AD1 | exact (wr_at_wmono _ _ _ _ WR WM1)
      | exact IN | intros X; discriminate X | intros _; split; [reflexivity | exact PERM] | exact CR3 | exact CR4
      | exact RH1 | exact PE | exact PM | exact (lb_own_wmono _ _ _ OWN WM1) | exact XP1 | exact RF1 | exact AC1 | exact S01 | exact AL ].
  Qed.
End EmpC.
